//@error-in-other-file: Unsat
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

struct FixedFilter {
    iter: Range,
}

impl Iterator for FixedFilter {
    type Item = <Range as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.iter.next() {
            if item >= 10 {
                return Some(item);
            }
        }
        None
    }
}

fn main() {
    let range = Range { start: 0, end: 5 };

    let mut adapter = FixedFilter { iter: range };

    let mut count = 0;
    let mut last = None;
    while let Some(i) = adapter.next() {
        count += 1;
        last = Some(i);
    }

    assert!(count > 0);
}
