// The Rust binding against the Lean reference: every row of the shared vectors (vbm-sse-vectors-1), on every cut: the whole input, one byte per chunk, each two-way split. A driver: it holds no input of its own;
// not part of the binding. VBM_SSE_VECTORS = the vectors.jsonl path (scripts/test_bindings.sh). The events collected from the reports, the last report's last event ID and the reconnection time must equal the row's.
use vbm_sse::{Event, Reader};

fn field<'a>(s: &'a str, key: &str) -> Option<(&'a str, &'a str)> {
    let pat = format!("\"{}\":\"", key);
    let a = s.find(&pat)? + pat.len();
    let n = s[a..].find('"')?;
    Some((&s[a..a + n], &s[a + n + 1..]))
}
fn unhex(h: &str) -> Vec<u8> { (0..h.len() / 2).map(|i| u8::from_str_radix(&h[2 * i..2 * i + 2], 16).unwrap()).collect() }

struct Row { input: Vec<u8>, events: Vec<Event>, last_event_id: Vec<u8>, retry: Option<u64> }

fn parse_row(line: &str) -> Row {
    let (input, rest) = field(line, "input").unwrap();
    let mut rest = &rest[rest.find("\"events\":[").unwrap() + 10..];
    let mut events = Vec::new();
    while rest.starts_with('{') {
        let (t, r) = field(rest, "type").unwrap();
        let (d, r) = field(r, "data").unwrap();
        let (i, r) = field(r, "last_event_id").unwrap();
        events.push(Event { type_: unhex(t), data: unhex(d), last_event_id: unhex(i) });
        rest = r.strip_prefix('}').unwrap();
        rest = rest.strip_prefix(',').unwrap_or(rest);
    }
    let (id, rest) = field(rest, "last_event_id").unwrap();
    let r = rest.split("\"retry\":").nth(1).unwrap().trim_end_matches('}').trim();
    Row { input: unhex(input), events, last_event_id: unhex(id), retry: if r == "null" { None } else { Some(r.parse().unwrap()) } }
}

fn run(chunks: &[&[u8]]) -> (Vec<Event>, Vec<u8>, Option<u64>) {
    let mut r = Reader::new().unwrap();
    let mut events = Vec::new();
    let mut last = None;
    for c in chunks {
        let rep = r.feed(c).unwrap();
        events.extend(rep.events.iter().cloned());
        last = Some((rep.last_event_id, rep.retry));
    }
    let (id, retry) = last.unwrap();
    (events, id, retry)
}

#[test]
fn vectors() {
    let path = std::env::var("VBM_SSE_VECTORS").expect("VBM_SSE_VECTORS is the vectors.jsonl path");
    let text = std::fs::read_to_string(path).unwrap();
    let (mut rows, mut runs) = (0usize, 0usize);
    for line in text.lines().filter(|l| !l.is_empty()) {
        let row = parse_row(line);
        let b = &row.input[..];
        let mut cuts: Vec<Vec<&[u8]>> = vec![vec![b]];
        for k in 0..=b.len() { cuts.push(vec![&b[..k], &b[k..]]); }
        if !b.is_empty() { cuts.push(b.chunks(1).collect()); }
        for cs in cuts {
            let (evs, id, retry) = run(&cs);
            runs += 1;
            assert!(evs == row.events && id == row.last_event_id && retry == row.retry, "row {}: {} chunk(s): the answer differs from the reference", rows, cs.len());
        }
        rows += 1;
    }
    assert!(rows > 100);
    println!("vectors: {} rows, {} cuts: events, last event ID and reconnection time equal the reference's", rows, runs);
}

#[test]
fn null_reader_is_refused_with_code_1() {
    let mut rep = vbm_sse::sys::vbm_sse_report { bytes: std::ptr::null(), nbytes: 0 };
    let rc = unsafe { vbm_sse::sys::vbm_sse_feed(std::ptr::null_mut(), std::ptr::null(), 0, &mut rep) };
    assert_eq!(rc, 1);
    assert_eq!(rc, vbm_sse::sys::VBM_SSE_ARG);
}
