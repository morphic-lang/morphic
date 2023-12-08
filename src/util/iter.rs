use id_collections::{Id, IdVec};

pub fn try_zip_exact<'a, K: Id, V, U>(
    lhs: &'a IdVec<K, V>,
    rhs: &'a IdVec<K, U>,
) -> Option<impl Iterator<Item = (K, &'a V, &'a U)>> {
    if lhs.len() == rhs.len() {
        Some(
            lhs.iter()
                .zip(rhs.values())
                .map(|((idx, v1), v2)| (idx, v1, v2)),
        )
    } else {
        None
    }
}
