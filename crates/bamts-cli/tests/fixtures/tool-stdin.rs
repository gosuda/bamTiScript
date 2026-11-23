use std::io::Read;

fn main() {
    let mut input = Vec::new();
    std::io::stdin()
        .read_to_end(&mut input)
        .expect("tool stdin is readable");
    assert!(input.is_empty(), "tool received compiler protocol input");

    let argument = std::env::args_os().nth(1).expect("tool argument");
    if argument == "--version" || argument == "/?" {
        println!("Microsoft (R) Incremental Linker Version 0.0");
        return;
    }

    let marker = std::env::var_os("BAMTS_STDIN_MARKER").expect("tool marker path");
    std::fs::write(marker, "eof").expect("tool marker is written");
    eprintln!("tool stdin reached EOF before linking");
    std::process::exit(42);
}
