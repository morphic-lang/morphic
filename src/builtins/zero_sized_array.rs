use inkwell::{context::Context, types::StructType};

pub fn def_types<'ctx>(
    context: &'ctx Context,
    array_type: &StructType<'ctx>,
    hole_type: &StructType<'ctx>,
) {
    let i64_type = context.i64_type();
    array_type.set_body(&[i64_type], false);
    hole_type.set_body(&[i64_type], false);
}

// fn define_funcs<'ctx>(
//     context: &'ctx Context,
//     target: &TargetData,
//     tal: &Tal<'ctx>,
//     item_retain: Option<FunctionValue<'ctx>>,
//     item_release: Option<FunctionValue<'ctx>>,
// ) {
//     assert!(item_retain.is_none());
//     assert!(item_release.is_none());
//
//     // define 'new'
//     {
//         let s = scope(self.interface.new, context, target);
//         s.ret(s.i64(0));
//     }
//
//     // define 'get'
//     {
//         let s = scope(self.interface.get, context, target);
//         let array = s.arg(0);
//         let idx = s.arg(1);
//
//         s.if_(s.uge(idx, array), |s| {
//             s.panic(
//                 "idx %d is out of bounds for array of length %d",
//                 &[idx, array],
//                 tal,
//             )
//         });
//
//         s.ret(s.undef(self.interface.item_type));
//     }
//
//     // define 'extract'
//     {
//         let s = scope(self.interface.extract, context, target);
//         let array = s.arg(0);
//         let idx = s.arg(1);
//
//         s.if_(s.uge(idx, array), |s| {
//             s.panic(
//                 "idx %d is out of bounds for array of length %d",
//                 &[idx, array],
//                 tal,
//             )
//         });
//
//         s.ret(s.make_tup(&[s.undef(self.interface.item_type), array]));
//     }
//
//     // define 'len'
//     {
//         let s = scope(self.interface.len, context, target);
//         let array = s.arg(0);
//         s.ret(array);
//     }
//
//     // define 'push'
//     {
//         let s = scope(self.interface.push, context, target);
//         let array = s.arg(0);
//         s.ret(s.add(array, s.i64(1)));
//     }
//
//     // define 'pop'
//     {
//         let s = scope(self.interface.pop, context, target);
//         let array = s.arg(0);
//
//         s.if_(s.eq(array, s.i64(0)), |s| {
//             s.panic("cannot pop array of length 0", &[], tal);
//         });
//
//         s.ret(s.make_tup(&[s.sub(array, s.i64(1)), s.undef(self.interface.item_type)]));
//     }
//
//     // define 'replace'
//     {
//         let s = scope(self.interface.replace, context, target);
//         let hole = s.arg(0);
//         // let item = s.arg(1); UNUSED ARGUMENT
//         s.ret(hole);
//     }
//
//     // define 'reserve'
//     {
//         let s = scope(self.interface.reserve, context, target);
//         let me = s.arg(0);
//         // let capacity = s.arg(1); UNUSED ARGUMENT
//         s.ret(me);
//     }
//
//     // define 'retain_array'
//     {
//         let s = scope(self.interface.retain_array, context, target);
//         // let array = s.arg(0); UNUSED ARGUMENT
//         s.ret_void();
//     }
//
//     // define 'release_array'
//     {
//         let s = scope(self.interface.release_array, context, target);
//         // let array = s.arg(0); UNUSED ARGUMENT
//         s.ret_void();
//     }
//
//     // define 'retain_hole'
//     {
//         let s = scope(self.interface.retain_hole, context, target);
//         // let hole = s.arg(0); UNUSED ARGUMENT
//         s.ret_void();
//     }
//
//     // define 'release_hole'
//     {
//         let s = scope(self.interface.release_hole, context, target);
//         // let hole = s.arg(0); UNUSED ARGUMENT
//         s.ret_void();
//     }
// }
