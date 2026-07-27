
/* Safe Rust API over the extracted ADAS scene checker. */

type ObjList<'a> =
    Corelib_Init_Datatypes_list<'a, &'a RocqRustExamples_SceneModel_obj<'a>>;

/// Per-object input, mirrored from the Python layer.
pub struct SceneObj {
    pub class: u8, // 0 vehicle, 1 pedestrian, 2 bicycle, 3 sign, 4 light
    pub x: i64, pub y: i64,
    pub vx: i64, pub vy: i64,
    pub w: i64, pub l: i64,
    pub conf: i64,
    pub target: bool,
    pub tl: i64,
}

fn objs_from<'a>(p: &'a Program, os: &[SceneObj]) -> &'a ObjList<'a> {
    let mut acc: &'a ObjList<'a> = p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for o in os.iter().rev() {
        let cls: &'a RocqRustExamples_SceneModel_oclass<'a> = match o.class {
            0 => p.alloc(RocqRustExamples_SceneModel_oclass::CVehicle(PhantomData)),
            1 => p.alloc(RocqRustExamples_SceneModel_oclass::CPedestrian(PhantomData)),
            2 => p.alloc(RocqRustExamples_SceneModel_oclass::CBicycle(PhantomData)),
            3 => p.alloc(RocqRustExamples_SceneModel_oclass::CSign(PhantomData)),
            _ => p.alloc(RocqRustExamples_SceneModel_oclass::CLight(PhantomData)),
        };
        let ob = p.alloc(RocqRustExamples_SceneModel_obj::mkObj(
            PhantomData, cls, o.x, o.y, o.vx, o.vy, o.w, o.l, o.conf, o.target, o.tl,
        ));
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, ob, acc));
    }
    acc
}

/// Run the checker. Returns (scene_ok, per-object (verdict, score, mask))
/// with verdict 0 = confirmed, 1 = low-confidence, 2 = implausible.
pub fn check(
    lanes: i64, lane_w: i64, curv: i64, limit: i64,
    ego_v: i64,
    objs: &[SceneObj],
) -> (bool, Vec<(u8, i64, i64)>) {
    let p = Program::new();
    let rd = p.alloc(RocqRustExamples_SceneModel_road::mkRoad(
        PhantomData, lanes, lane_w, curv, limit,
    ));
    let rep = p.RocqRustExamples_SceneModel_scene_demo(rd, ego_v, objs_from(&p, objs));
    match rep {
        RocqRustExamples_SceneModel_report::mkReport(_, ok, entries) => {
            let mut out = Vec::new();
            let mut l = *entries;
            loop {
                match l {
                    Corelib_Init_Datatypes_list::nil(_) => break,
                    Corelib_Init_Datatypes_list::cons(_, e, rest) => {
                        match e {
                            RocqRustExamples_SceneModel_entry::mkEntry(_, v, sc, mask) => {
                                let vc = match v {
                                    RocqRustExamples_SceneModel_verdict::VConfirmed(_) => 0u8,
                                    RocqRustExamples_SceneModel_verdict::VLow(_) => 1,
                                    RocqRustExamples_SceneModel_verdict::VImplausible(_) => 2,
                                };
                                out.push((vc, *sc, *mask));
                            }
                        }
                        l = *rest;
                    }
                }
            }
            (*ok, out)
        }
    }
}
