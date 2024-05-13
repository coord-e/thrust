#[derive(Debug, Clone)]
pub struct TupleProj {
    index: usize,
}

impl std::fmt::Display for TupleProj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t{}", self.index)
    }
}

impl TupleProj {
    pub fn new(index: usize) -> Self {
        Self { index }
    }
}

#[derive(Debug, Clone)]
pub struct TupleTypeName {
    size: usize,
}

impl std::fmt::Display for TupleTypeName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "T{}", self.size)
    }
}

impl TupleTypeName {
    pub fn new(size: usize) -> Self {
        Self { size }
    }
}

#[derive(Debug, Clone)]
pub struct TupleCtor {
    size: usize,
}

impl std::fmt::Display for TupleCtor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "mk_tuple{}", self.size)
    }
}

impl TupleCtor {
    pub fn new(size: usize) -> Self {
        Self { size }
    }
}
