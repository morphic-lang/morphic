#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Purity {
    Pure,
    Impure,
}

pub fn meet(p1: Purity, p2: Purity) -> Purity {
    match (p1, p2) {
        (Purity::Pure, Purity::Pure) => Purity::Pure,
        _ => Purity::Impure,
    }
}
