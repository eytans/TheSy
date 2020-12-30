/// a macro used for debugging
/// prints only when running tests
// #[proc_macro]
pub(crate) fn test_print(str: &String){
    if cfg!(test){
        println!("{}", str);
    }
}

/// a macro for calling functions only when testing
/// In our use, good for exporting dot files to track changes in e-graph
pub(crate) fn test_call_fn(f: &dyn Fn()->()){
    if cfg!(test){
        f();
    }
}
