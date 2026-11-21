//! Strongly connected components, for ordering definitions and finding
//! the functions that call each other.

struct Tarjan<'g> {
    edges: &'g [Vec<usize>],
    index: Vec<Option<usize>>,
    low: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    next: usize,
    out: Vec<Vec<usize>>,
}

impl Tarjan<'_> {
    fn visit(&mut self, v: usize) {
        let i = self.next;
        self.next += 1;
        if let (Some(a), Some(b), Some(c)) =
            (self.index.get_mut(v), self.low.get_mut(v), self.on_stack.get_mut(v))
        {
            *a = Some(i);
            *b = i;
            *c = true;
        }
        self.stack.push(v);
        for &w in self.edges.get(v).map_or(&[][..], Vec::as_slice) {
            match self.index.get(w).copied().flatten() {
                None => {
                    self.visit(w);
                    self.lower(v, self.low.get(w).copied());
                }
                Some(wi) if self.on_stack.get(w).copied().unwrap_or(false) => self.lower(v, Some(wi)),
                Some(_) => {}
            }
        }
        if self.low.get(v).copied() == Some(i) {
            let mut comp = Vec::new();
            while let Some(w) = self.stack.pop() {
                if let Some(s) = self.on_stack.get_mut(w) {
                    *s = false;
                }
                comp.push(w);
                if w == v {
                    break;
                }
            }
            comp.sort_unstable();
            self.out.push(comp);
        }
    }

    fn lower(&mut self, v: usize, to: Option<usize>) {
        if let (Some(l), Some(to)) = (self.low.get_mut(v), to) {
            *l = (*l).min(to);
        }
    }
}

/// The components of the graph, each after every component it has an edge to.
pub(crate) fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut t = Tarjan {
        edges,
        index: vec![None; n],
        low: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        next: 0,
        out: Vec::new(),
    };
    for v in 0..n {
        if t.index.get(v).copied().flatten().is_none() {
            t.visit(v);
        }
    }
    t.out
}
