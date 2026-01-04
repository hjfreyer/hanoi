/// A trait for debugging purposes
pub trait DebugWith<C> {
    /// The output type for debugging
    type Output<'a>: 'a + std::fmt::Debug
    where
        Self: 'a,
        C: 'a;

    /// Convert self to the output type using the provided context
    fn convert<'a>(&self, context: &'a C) -> Self::Output<'a>;
}

impl<C, T> DebugWith<C> for Vec<T>
where
    T: DebugWith<C>,
{
    type Output<'a>
        = Vec<T::Output<'a>>
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, context: &'a C) -> Self::Output<'a> {
        self.iter().map(|item| item.convert(context)).collect()
    }
}

impl<C, K, V> DebugWith<C> for typed_index_collections::TiVec<K, V>
where
    K: From<usize> + 'static + std::fmt::Debug,
    V: DebugWith<C>,
{
    type Output<'a>
        = typed_index_collections::TiVec<K, V::Output<'a>>
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, context: &'a C) -> Self::Output<'a> {
        self.iter().map(|v| v.convert(context)).collect()
    }
}

impl<C> DebugWith<C> for usize {
    type Output<'a>
        = usize
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, _context: &'a C) -> Self::Output<'a> {
        *self
    }
}

impl<C> DebugWith<C> for bool {
    type Output<'a>
        = bool
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, _context: &'a C) -> Self::Output<'a> {
        *self
    }
}

impl<C> DebugWith<C> for char {
    type Output<'a>
        = char
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, _context: &'a C) -> Self::Output<'a> {
        *self
    }
}

// Tuple implementations
impl<C, T1> DebugWith<C> for (T1,)
where
    T1: DebugWith<C>,
{
    type Output<'a>
        = (T1::Output<'a>,)
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, context: &'a C) -> Self::Output<'a> {
        (self.0.convert(context),)
    }
}

impl<C, T1, T2> DebugWith<C> for (T1, T2)
where
    T1: DebugWith<C>,
    T2: DebugWith<C>,
{
    type Output<'a>
        = (T1::Output<'a>, T2::Output<'a>)
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, context: &'a C) -> Self::Output<'a> {
        (self.0.convert(context), self.1.convert(context))
    }
}

impl<C, T1, T2, T3> DebugWith<C> for (T1, T2, T3)
where
    T1: DebugWith<C>,
    T2: DebugWith<C>,
    T3: DebugWith<C>,
{
    type Output<'a>
        = (T1::Output<'a>, T2::Output<'a>, T3::Output<'a>)
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, context: &'a C) -> Self::Output<'a> {
        (
            self.0.convert(context),
            self.1.convert(context),
            self.2.convert(context),
        )
    }
}

impl<C, T1, T2, T3, T4> DebugWith<C> for (T1, T2, T3, T4)
where
    T1: DebugWith<C>,
    T2: DebugWith<C>,
    T3: DebugWith<C>,
    T4: DebugWith<C>,
{
    type Output<'a>
        = (
        T1::Output<'a>,
        T2::Output<'a>,
        T3::Output<'a>,
        T4::Output<'a>,
    )
    where
        Self: 'a,
        C: 'a;

    fn convert<'a>(&self, context: &'a C) -> Self::Output<'a> {
        (
            self.0.convert(context),
            self.1.convert(context),
            self.2.convert(context),
            self.3.convert(context),
        )
    }
}
