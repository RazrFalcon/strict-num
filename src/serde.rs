use serde::{Serialize, Serializer};

macro_rules! impl_serialize_num {
    ($($T:ident,)+) => {
        $(
            impl Serialize for crate::$T {
                fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
                where
                    S: Serializer,
                {
                    self.get().serialize(serializer)
                }
            }
        )+
    }
}

impl_serialize_num! {
    FiniteF32,
    FiniteF64,
    PositiveF32,
    PositiveF64,
    NonZeroPositiveF32,
    NonZeroPositiveF64,
    NormalizedF32,
    NormalizedF64,
}
