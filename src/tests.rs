pub fn init_logging() {
    use simplelog::*;

    let mut builder = ConfigBuilder::new();
    builder.add_filter_ignore("egg".parse().unwrap());
    let config = builder.build();
    TermLogger::init(LevelFilter::Info, config, TerminalMode::Mixed).unwrap();
}