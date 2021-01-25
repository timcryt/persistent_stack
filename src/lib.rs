use std::sync::Arc;

struct PersistentStackNode<T> {
    data: T,
    parent: Option<Arc<PersistentStackNode<T>>>,
}

/// # Concurrent persistent stack
/// Supportted operations:
/// - clone *O*(1)
/// - push *O*(1)
/// - iterate *O*(n)
///
/// ```rust
/// use persistent_stack::PersistentStack;
///
/// let mut s1 = PersistentStack::new();
/// s1.push(1);
/// let mut s2 = s1.clone();
/// std::thread::spawn(move || {
///     s2.push(2);
///     assert_eq!(s2.iter().copied().collect::<Vec<_>>(), vec![2, 1]);
///     std::thread::sleep(std::time::Duration::from_millis(20));
///     s2.push(4);
///     assert_eq!(s2.iter().copied().collect::<Vec<_>>(), vec![4, 2, 1]);
/// });
/// s1.push(3);
/// assert_eq!(s1.iter().copied().collect::<Vec<_>>(), vec![3, 1]);
/// std::thread::sleep(std::time::Duration::from_millis(20));
/// s1.push(5);
/// assert_eq!(s1.iter().copied().collect::<Vec<_>>(), vec![5, 3, 1]);
/// ```
pub struct PersistentStack<T>(Option<Arc<PersistentStackNode<T>>>);

impl<T> Default for PersistentStack<T> {
    fn default() -> PersistentStack<T> {
        PersistentStack(None)
    }
}

impl<T> Clone for PersistentStack<T> {
    fn clone(&self) -> Self {
        PersistentStack(self.0.as_ref().map(|x| Arc::clone(x)))
    }
}

impl<T> PersistentStack<T> {
    /// Creates new empty persistent stack
    ///
    /// ```rust
    /// use persistent_stack::PersistentStack;
    ///
    /// let s = PersistentStack::<i32>::new();
    /// assert!(s.into_iter().next().is_none())
    /// ```
    pub fn new() -> PersistentStack<T> {
        Self::default()
    }

    /// Pushes `data` to end of `self` (affects only current copy of stack)
    ///
    /// ```rust
    /// use persistent_stack::PersistentStack;
    /// use std::sync::Arc;
    ///
    /// let mut s1 = PersistentStack::new();
    /// s1.push(1);
    /// let mut s2 = s1.clone();
    /// s2.push(2);
    /// assert_eq!(s1.into_iter().collect::<Vec<_>>(), [&1]);
    /// assert_eq!(s2.into_iter().collect::<Vec<_>>(), [&2, &1]);
    pub fn push(&mut self, data: T) {
        let node = PersistentStackNode {
            data,
            parent: self.0.as_ref().map(|x| Arc::clone(x)),
        };
        *self = PersistentStack(Some(Arc::new(node)));
    }

    /// Creates iterator over `self` by reference
    ///
    /// ```rust
    /// use persistent_stack::PersistentStack;
    ///
    /// let mut s = PersistentStack::new();
    /// s.push(1);
    /// s.push(2);
    /// s.push(3);
    /// assert_eq!(s.iter().collect::<Vec<_>>(), [&3, &2, &1]);
    /// s.push(4); // s didn't move out
    pub fn iter(&self) -> PersistentStackIter<T> {
        PersistentStackIter(self.0.as_deref())
    }
}

/// Iterator over persistent stack
pub struct PersistentStackIter<'a, T>(Option<&'a PersistentStackNode<T>>);

impl<'a, T> IntoIterator for &'a PersistentStack<T> {
    type IntoIter = PersistentStackIter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        PersistentStackIter(self.0.as_deref())
    }
}

impl<'a, T> Iterator for PersistentStackIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.map(|node| {
            self.0 = node.parent.as_deref();
            &node.data
        })
    }
}

mod tests {
    #[test]
    fn test_persistent_stack() {
        let mut s1 = crate::PersistentStack::new();
        s1.push(1);
        s1.push(2);
        let mut s2 = s1.clone();
        s1.push(3);
        s2.push(4);
        assert_eq!(s1.into_iter().map(|x| *x).collect::<Vec<_>>(), [3, 2, 1]);
        assert_eq!(s2.into_iter().map(|x| *x).collect::<Vec<_>>(), [4, 2, 1]);
    }
}
