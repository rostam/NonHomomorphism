// nhcli <G.g6> <H.g6> [timeout_s]  -> prints value, exact flag, mapping
use nonhom_param::*;
use std::time::{Duration, Instant};
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let g = from_graph6(&a[1]).expect("bad G");
    let h = from_graph6(&a[2]).expect("bad H");
    let t = a.get(3).and_then(|s| s.parse().ok()).unwrap_or(60u64);
    let (prog, handle) = solve_in_background(g, h);
    let start = Instant::now();
    while !prog.is_finished() {
        if start.elapsed() > Duration::from_secs(t) { prog.cancel(); }
        std::thread::sleep(Duration::from_millis(20));
    }
    let s = handle.join().unwrap();
    println!("{{\"value\":{},\"exact\":{},\"mapping\":{:?},\"secs\":{:.2}}}", s.value, s.exact, s.mapping, start.elapsed().as_secs_f64());
}
