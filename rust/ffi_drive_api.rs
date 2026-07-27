
/* Safe Rust API over the extracted drive-mode FSM. */

type DEvList<'a> =
    Corelib_Init_Datatypes_list<'a, &'a RocqRustExamples_DriveModeFsm_event<'a>>;

/// Events: (0, gear, v) = shift request; (1, _, _) = fault; (2, _, v) = clear.
/// Gears: 0=Park 1=Reverse 2=Neutral 3=Drive.
fn devents_from<'a>(p: &'a Program, es: &[(u8, u8, i64)]) -> &'a DEvList<'a> {
    let mut acc: &'a DEvList<'a> = p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &(tag, g, v) in es.iter().rev() {
        let e: &'a RocqRustExamples_DriveModeFsm_event<'a> = match tag {
            0 => {
                let gear = match g {
                    0 => p.alloc(RocqRustExamples_DriveModeFsm_gear::GPark(PhantomData)),
                    1 => p.alloc(RocqRustExamples_DriveModeFsm_gear::GReverse(PhantomData)),
                    2 => p.alloc(RocqRustExamples_DriveModeFsm_gear::GNeutral(PhantomData)),
                    _ => p.alloc(RocqRustExamples_DriveModeFsm_gear::GDrive(PhantomData)),
                };
                p.alloc(RocqRustExamples_DriveModeFsm_event::EvShift(PhantomData, gear, v))
            }
            1 => p.alloc(RocqRustExamples_DriveModeFsm_event::EvFault(PhantomData)),
            _ => p.alloc(RocqRustExamples_DriveModeFsm_event::EvFaultClear(PhantomData, v)),
        };
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, e, acc));
    }
    acc
}

/// Run from Park; final mode as 0=P 1=R 2=N 3=D 4=Fault.
pub fn run(events: &[(u8, u8, i64)]) -> u8 {
    let p = Program::new();
    match p.RocqRustExamples_DriveModeFsm_drive_demo(devents_from(&p, events)) {
        RocqRustExamples_DriveModeFsm_mode::MPark(_) => 0,
        RocqRustExamples_DriveModeFsm_mode::MReverse(_) => 1,
        RocqRustExamples_DriveModeFsm_mode::MNeutral(_) => 2,
        RocqRustExamples_DriveModeFsm_mode::MDrive(_) => 3,
        RocqRustExamples_DriveModeFsm_mode::MFault(_) => 4,
    }
}
