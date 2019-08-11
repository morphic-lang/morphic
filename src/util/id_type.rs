pub trait Id: Clone {
    fn from_index(idx: usize) -> Self;
    fn to_index(&self) -> usize;
}

macro_rules! id_type_trait_impl {
    ($name:ident) => {
        impl $crate::util::id_type::Id for $name {
            fn from_index(idx: usize) -> Self {
                $name(idx)
            }

            fn to_index(&self) -> usize {
                self.0
            }
        }

        // Custom Debug impl avoids multi-line formatting when formatted with {:#?}
        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                write!(f, "{}({})", stringify!($name), self.0)
            }
        }
    };
}

macro_rules! id_type {
    (pub $name:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $name(pub usize);

        id_type_trait_impl!($name);
    };

    ($name:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        struct $name(usize);

        id_type_trait_impl!($name);
    };
}
