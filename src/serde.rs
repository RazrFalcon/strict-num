use core::fmt;

use serde::{
    de::{Error, Unexpected, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

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

macro_rules! impl_deserialize_num {
    ($expecting:expr, $primitive:ident, $strict_num:ident, $deserialize:ident $($method:ident!($($val:ident : $visit:ident)*);)*) => {
        impl<'de> Deserialize<'de> for crate::$strict_num {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct StrictNumVisitor;

                impl<'de> Visitor<'de> for StrictNumVisitor {
                    type Value = crate::$strict_num;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str(concat!($expecting, stringify!($primitive)))
                    }

                    $($($method!($primitive $val : $visit);)*)*
                }

                deserializer.$deserialize(StrictNumVisitor)
            }
        }
    };
}

macro_rules! num_self {
    ($primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if let Some(strict_num) = Self::Value::new(v) {
                Ok(strict_num)
            } else {
                Err(Error::invalid_value(Unexpected::Float(v as f64), &self))
            }
        }
    };
}

macro_rules! num_as_self {
    ($primitive:ident $ty:ident : $visit:ident) => {
        fn $visit<E>(self, v: $ty) -> Result<Self::Value, E>
        where
            E: Error,
        {
            if let Some(strict_num) = Self::Value::new(v as $primitive) {
                Ok(strict_num)
            } else {
                Err(Error::invalid_value(Unexpected::Float(v as f64), &self))
            }
        }
    };
}

impl_deserialize_num! {
    "a finite ",
    f32, FiniteF32, deserialize_f32
    num_self!(f32:visit_f32);
    num_as_self!(f64:visit_f64);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    "a finite ",
    f64, FiniteF64, deserialize_f64
    num_self!(f64:visit_f64);
    num_as_self!(f32:visit_f32);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    "a positive ",
    f32, PositiveF32, deserialize_f32
    num_self!(f32:visit_f32);
    num_as_self!(f64:visit_f64);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    "a positive ",
    f64, PositiveF64, deserialize_f64
    num_self!(f64:visit_f64);
    num_as_self!(f32:visit_f32);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    "a nonzero positive ",
    f32, NonZeroPositiveF32, deserialize_f32
    num_self!(f32:visit_f32);
    num_as_self!(f64:visit_f64);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    "a nonzero positive ",
    f64, NonZeroPositiveF64, deserialize_f64
    num_self!(f64:visit_f64);
    num_as_self!(f32:visit_f32);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    "a normalized ",
    f32, NormalizedF32, deserialize_f32
    num_self!(f32:visit_f32);
    num_as_self!(f64:visit_f64);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

impl_deserialize_num! {
    "a normalized ",
    f64, NormalizedF64, deserialize_f64
    num_self!(f64:visit_f64);
    num_as_self!(f32:visit_f32);
    num_as_self!(i8:visit_i8 i16:visit_i16 i32:visit_i32 i64:visit_i64);
    num_as_self!(u8:visit_u8 u16:visit_u16 u32:visit_u32 u64:visit_u64);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_serialize() {
        let num = crate::FiniteF32::new(0.0).unwrap();
        assert_eq!(serde_json::to_string(&num).unwrap(), "0.0");

        let num = crate::FiniteF64::new(0.0).unwrap();
        assert_eq!(serde_json::to_string(&num).unwrap(), "0.0");

        let num = crate::PositiveF32::new(0.0).unwrap();
        assert_eq!(serde_json::to_string(&num).unwrap(), "0.0");

        let num = crate::PositiveF64::new(0.0).unwrap();
        assert_eq!(serde_json::to_string(&num).unwrap(), "0.0");

        let num = crate::NonZeroPositiveF32::new(1.0).unwrap();
        assert_eq!(serde_json::to_string(&num).unwrap(), "1.0");

        let num = crate::NonZeroPositiveF64::new(1.0).unwrap();
        assert_eq!(serde_json::to_string(&num).unwrap(), "1.0");

        let num = crate::NormalizedF32::new(0.0).unwrap();
        assert_eq!(serde_json::to_string(&num).unwrap(), "0.0");

        let num = crate::NormalizedF64::new(0.0).unwrap();
        assert_eq!(serde_json::to_string(&num).unwrap(), "0.0");
    }

    #[test]
    fn test_deserialize() {
        let src = "0.0";
        let num: crate::FiniteF32 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 0.0);

        let src = "0";
        let num: crate::FiniteF32 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 0.0);

        let src = "0.0";
        let num: crate::FiniteF64 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 0.0);

        let src = "0";
        let num: crate::FiniteF64 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 0.0);

        let src = "-1.0";
        assert!(serde_json::from_str::<crate::PositiveF32>(src).is_err());

        let src = "0";
        let num: crate::PositiveF32 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 0.0);

        let src = "-1.0";
        assert!(serde_json::from_str::<crate::PositiveF64>(src).is_err());

        let src = "0";
        let num: crate::PositiveF64 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 0.0);

        let src = "0.0";
        assert!(serde_json::from_str::<crate::NonZeroPositiveF32>(src).is_err());

        let src = "1.0";
        let num: crate::NonZeroPositiveF32 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 1.0);

        let src = "0.0";
        assert!(serde_json::from_str::<crate::NonZeroPositiveF64>(src).is_err());

        let src = "1.0";
        let num: crate::NonZeroPositiveF64 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 1.0);

        let src = "-1.0";
        assert!(serde_json::from_str::<crate::NormalizedF32>(src).is_err());

        let src = "2.0";
        assert!(serde_json::from_str::<crate::NormalizedF32>(src).is_err());

        let src = "0.0";
        let num: crate::NormalizedF32 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 0.0);

        let src = "-1.0";
        assert!(serde_json::from_str::<crate::NormalizedF64>(src).is_err());

        let src = "2.0";
        assert!(serde_json::from_str::<crate::NormalizedF64>(src).is_err());

        let src = "0.0";
        let num: crate::NormalizedF64 = serde_json::from_str(src).unwrap();
        assert_eq!(num.get(), 0.0);
    }
}
