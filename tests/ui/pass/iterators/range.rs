//@check-pass
//@compile-flags: -C debug-assertions=off

struct Range {
    start: i64,
    end: i64,
}

impl Iterator for Range {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let mut count = 0;
    while let Some(i) = range.next() {
        count += 1;
    }

    assert!(count == 5);
    assert!(range.start == count);
}
