#!/usr/bin/env ruby
# Ruby caller for the Rocq-verified cores, via the stdlib Fiddle FFI —
# zero gems, straight onto the C ABI (see include/rocq_ffi.h for the
# contract, including the per-function proved domains a binding must
# enforce; this demo enforces the ones it uses inline).
#
# Run:  make interop      (or: ruby interop/ruby/demo.rb path/to/librocq_ffi.so)

require "fiddle"

LIB = Fiddle.dlopen(ARGV[0] ||
  File.expand_path("../../rust/rocq_ffi/target/release/librocq_ffi.so", __dir__))

I64 = Fiddle::TYPE_LONG_LONG
U64 = Fiddle::TYPE_ULONG_LONG
PTR = Fiddle::TYPE_VOIDP
SZ  = Fiddle::TYPE_SIZE_T
I32 = Fiddle::TYPE_INT

def fn(name, args, ret = Fiddle::TYPE_INT)
  Fiddle::Function.new(LIB[name.to_s], args, ret)
end

SORT     = fn(:rocq_sort_i64,   [PTR, SZ, PTR])
FLETCHER = fn(:rocq_fletcher16, [PTR, SZ, PTR, PTR])
POW_MOD  = fn(:rocq_pow_mod,    [U64, U64, U64, PTR])
RSS      = fn(:rocq_rss_check,  [I64, I64, I64, I64, I64, I64, I64, PTR, PTR])

def i64_buf(vals) = Fiddle::Pointer[vals.pack("q*")]
def out(n = 1) = Fiddle::Pointer.malloc(8 * n)

puts "=== Ruby caller (stdlib Fiddle): Rocq-verified cores ===\n\n"

# verified insertion sort
xs = [5, 3, 8, 1, 9, -4]
sorted = out(xs.size)
raise unless SORT.call(i64_buf(xs), xs.size, sorted).zero?
result = sorted[0, 8 * xs.size].unpack("q*")
puts "sort      : #{xs.inspect} -> #{result.inspect}"
raise unless result == xs.sort

# Fletcher-16 — enforcing the property domain [0,254] ourselves,
# as the header instructs a binding to do
frame = [0x10, 0x22, 0x00, 0x7F, 0x22, 0x01, 0x54]
raise "symbol outside [0,254]" unless frame.all? { |d| (0..254).cover?(d) }
s1, s2 = out, out
raise unless FLETCHER.call(i64_buf(frame), frame.size, s1, s2).zero?
ck = 256 * s2[0, 8].unpack1("q") + s1[0, 8].unpack1("q")
puts format("fletcher16: frame checksum = 0x%04x", ck)

# verified modular exponentiation vs Ruby's built-in
m, b, e = 1_000_000_007, 2, 10**15
o = out
raise unless POW_MOD.call(m, b, e, o).zero?
got = o[0, 8].unpack1("Q")
raise unless got == b.pow(e, m)
puts "pow_mod   : #{b}^#{e} mod #{m} = #{got}  (matches Ruby's Integer#pow)"

# RSS envelope
safe = Fiddle::Pointer.malloc(1)
margin = out
raise unless RSS.call(400, 800, 3000, 2000, 1500, 10, 300, safe, margin).zero?
puts "rss       : gap 30 m at 20 vs 15 m/s -> #{safe[0, 1].unpack1('C') == 1 ? 'SAFE' : 'UNSAFE'}"
raise unless safe[0, 1].unpack1("C").zero?
raise unless RSS.call(400, 800, 8000, 2000, 1500, 10, 300, safe, margin).zero?
puts "rss       : gap 80 m at 20 vs 15 m/s -> #{safe[0, 1].unpack1('C') == 1 ? 'SAFE' : 'UNSAFE'}"
raise unless safe[0, 1].unpack1("C") == 1

puts "\nRuby caller: all checks passed."
