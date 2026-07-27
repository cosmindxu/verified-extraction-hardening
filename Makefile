ROCQ_MAKEFILE := RocqMakefile

# Driver #1: hand-built remaps, no OCaml plugin needed.
EXTRACTED_1 := extracted/InsertionSort.rs.out
CRATE_1     := rust/insertion_sort
MAIN_1      := $(CRATE_1)/src/main.rs
BIN_1       := $(CRATE_1)/target/release/insertion_sort

# Driver #2: `Rust Extract` vernacular from rocq-typed-extraction-plugin.
EXTRACTED_2 := extracted/InsertionSortPlugin.rs.out
CRATE_2     := rust/insertion_sort_plugin
MAIN_2      := $(CRATE_2)/src/main.rs
BIN_2       := $(CRATE_2)/target/release/insertion_sort_plugin

# Example #2: verified trading analytics.
EXTRACTED_T := extracted/Trading.rs.out
EXTRACTED_TC := extracted/TradingChecked.rs.out
EXTRACTED_RLE := extracted/Rle.rs.out
EXTRACTED_MX := extracted/ModExp.rs.out
EXTRACTED_FSM := extracted/OrderFsm.rs.out
# Safety-critical batch: extracted source -> FFI module -> API suffix
SAFETY_MODS := drive_fsm energy_fsm pid thermo mpc fusion scene scene_world fletcher rss
SAFETY_SRC_drive_fsm := DriveModeFsm
SAFETY_SRC_energy_fsm := HybridEnergyFsm
SAFETY_SRC_pid := Pid
SAFETY_SRC_thermo := Hysteresis
SAFETY_SRC_mpc := Mpc
SAFETY_SRC_fusion := SensorFusion
SAFETY_SRC_scene := SceneModel
SAFETY_SRC_scene_world := SceneWorld
SAFETY_SRC_fletcher := Fletcher
SAFETY_SRC_rss := Rss
SAFETY_API_drive_fsm := drive
SAFETY_API_energy_fsm := energy
SAFETY_API_pid := pid
SAFETY_API_thermo := thermo
SAFETY_API_mpc := mpc
SAFETY_API_fusion := fusion
SAFETY_API_scene := scene
SAFETY_API_scene_world := scene_world
SAFETY_API_fletcher := fletcher
SAFETY_API_rss := rss
CRATE_T     := rust/trading
MAIN_T      := $(CRATE_T)/src/main.rs
BIN_T       := $(CRATE_T)/target/release/trading

# Python bindings: one cdylib holding both extracted modules.
CRATE_F  := rust/rocq_ffi
FFI_LIB  := $(CRATE_F)/target/release/librocq_ffi.so

.PHONY: all rocq rust run compare trading python interop clean

all: run

$(ROCQ_MAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(ROCQ_MAKEFILE)

# Compiles the proofs and, via the Redirects in the two extraction drivers,
# writes both .rs.out files.
rocq: $(ROCQ_MAKEFILE)
	$(MAKE) -f $(ROCQ_MAKEFILE)

# Generated code + hand-written driver -> a single main.rs.
# The plugin prints `Debug: ... executed in: ...s` timing lines; strip them.
$(MAIN_1): rocq rust/main_suffix.rs
	@mkdir -p $(CRATE_1)/src
	sed '/^Debug/d' $(EXTRACTED_1) > $@
	cat rust/main_suffix.rs >> $@

$(MAIN_2): rocq rust/main_suffix.rs
	@mkdir -p $(CRATE_2)/src
	sed '/^Debug/d' $(EXTRACTED_2) > $@
	cat rust/main_suffix.rs >> $@

$(MAIN_T): rocq rust/trading_main.rs
	@mkdir -p $(CRATE_T)/src
	sed '/^Debug/d' $(EXTRACTED_T) > $@
	cat rust/trading_main.rs >> $@

rust: $(MAIN_1) $(MAIN_2) $(MAIN_T)
	cd $(CRATE_1) && cargo build --release
	cd $(CRATE_2) && cargo build --release
	cd $(CRATE_T) && cargo build --release

run: rust
	@echo; echo "########## insertion sort, driver #1: hand-built remaps ##########"; echo
	./$(BIN_1)
	@echo; echo "########## insertion sort, driver #2: Rust Extract ##########"; echo
	./$(BIN_2)
	@echo; echo "########## trading analytics ##########"; echo
	./$(BIN_T)

# --- Python bindings -------------------------------------------------
# Each extracted module keeps its own Program/arena/datatypes, so they go
# into separate Rust modules; the generated code names types identically.
$(CRATE_F)/src/sorting.rs: rocq rust/ffi_sorting_api.rs
	@mkdir -p $(CRATE_F)/src
	sed '/^Debug/d' $(EXTRACTED_1) > $@
	cat rust/ffi_sorting_api.rs >> $@

$(CRATE_F)/src/trading.rs: rocq rust/ffi_trading_api.rs
	@mkdir -p $(CRATE_F)/src
	sed '/^Debug/d' $(EXTRACTED_T) > $@
	cat rust/ffi_trading_api.rs >> $@

$(CRATE_F)/src/trading_checked.rs: rocq rust/ffi_trading_api.rs
	@mkdir -p $(CRATE_F)/src
	sed '/^Debug/d' $(EXTRACTED_TC) > $@
	cat rust/ffi_trading_api.rs >> $@

$(CRATE_F)/src/rle.rs: rocq rust/ffi_rle_api.rs
	@mkdir -p $(CRATE_F)/src
	sed '/^Debug/d' $(EXTRACTED_RLE) > $@
	cat rust/ffi_rle_api.rs >> $@

$(CRATE_F)/src/modexp.rs: rocq rust/ffi_modexp_api.rs
	@mkdir -p $(CRATE_F)/src
	sed '/^Debug/d' $(EXTRACTED_MX) > $@
	cat rust/ffi_modexp_api.rs >> $@

$(CRATE_F)/src/order_fsm.rs: rocq rust/ffi_fsm_api.rs
	@mkdir -p $(CRATE_F)/src
	sed '/^Debug/d' $(EXTRACTED_FSM) > $@
	cat rust/ffi_fsm_api.rs >> $@

define SAFETY_RULE
$$(CRATE_F)/src/$(1).rs: rocq rust/ffi_$$(SAFETY_API_$(1))_api.rs
	@mkdir -p $$(CRATE_F)/src
	sed '/^Debug/d' extracted/$$(SAFETY_SRC_$(1)).rs.out > $$@
	cat rust/ffi_$$(SAFETY_API_$(1))_api.rs >> $$@
endef
$(foreach m,$(SAFETY_MODS),$(eval $(call SAFETY_RULE,$(m))))

FFI_GENERATED := $(CRATE_F)/src/sorting.rs $(CRATE_F)/src/trading.rs \
	$(CRATE_F)/src/trading_checked.rs $(CRATE_F)/src/rle.rs \
	$(CRATE_F)/src/modexp.rs $(CRATE_F)/src/order_fsm.rs \
	$(foreach m,$(SAFETY_MODS),$(CRATE_F)/src/$(m).rs)

$(FFI_LIB): $(FFI_GENERATED) $(CRATE_F)/src/lib.rs
	cd $(CRATE_F) && cargo build --release

python: $(FFI_LIB)
	@echo
	cd python && python3 demo.py
	@echo
	cd python && python3 demo_more.py
	@echo
	cd python && python3 demo_safety.py
	@echo
	cd python && python3 demo_scene.py
	@echo
	cd python && python3 demo_integrity.py

# Cross-language interop demos: C and Ruby directly on the C ABI.
INTEROP_C := interop/c/demo
$(INTEROP_C): interop/c/demo.c include/rocq_ffi.h $(FFI_LIB)
	gcc -Wall -Wextra -O2 -Iinclude interop/c/demo.c \
	  -L$(CRATE_F)/target/release -lrocq_ffi \
	  -Wl,-rpath,'$$ORIGIN/../../rust/rocq_ffi/target/release' \
	  -o $@

interop: $(INTEROP_C)
	@echo
	./$(INTEROP_C)
	@echo
	ruby interop/ruby/demo.rb $(FFI_LIB)

# Just the trading example.
trading: $(MAIN_T)
	cd $(CRATE_T) && cargo build --release
	@echo
	./$(BIN_T)

# Do the two pipelines agree, on the generated source and at runtime?
compare: rust
	@echo "--- generated source (Debug timing lines stripped) ---"
	@diff $(MAIN_1) $(MAIN_2) > /dev/null && echo "IDENTICAL" \
	  || diff $(MAIN_1) $(MAIN_2) | sed -n '1,40p'
	@echo
	@echo "--- program output ---"
	@./$(BIN_1) > /tmp/out1.txt; ./$(BIN_2) > /tmp/out2.txt; \
	 diff /tmp/out1.txt /tmp/out2.txt > /dev/null \
	   && echo "IDENTICAL" || diff /tmp/out1.txt /tmp/out2.txt

clean:
	-$(MAKE) -f $(ROCQ_MAKEFILE) clean 2>/dev/null || true
	rm -f $(ROCQ_MAKEFILE) $(ROCQ_MAKEFILE).conf
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux
	rm -f extracted/*.rs.out
	rm -f $(MAIN_1) $(MAIN_2) $(MAIN_T)
	rm -f $(FFI_GENERATED)
	rm -rf $(CRATE_1)/target $(CRATE_2)/target $(CRATE_T)/target $(CRATE_F)/target
	rm -rf python/__pycache__
	rm -f interop/c/demo
