use std::sync::Arc;
struct PersistentStackNode<T> {
    data: Arc<T>,
    parent: Option<Arc<PersistentStackNode<T>>>,
}
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
    pub fn new() -> PersistentStack<T> {
        Self::default()
    }
}

pub struct PersistentStackIter<T>(PersistentStack<T>);

impl<T> Clone for PersistentStackIter<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> IntoIterator for PersistentStack<T> {
    type IntoIter = PersistentStackIter<T>;
    type Item = Arc<T>;

    fn into_iter(self) -> Self::IntoIter {
        PersistentStackIter(self)
    }
}

impl<T> Iterator for PersistentStackIter<T> {
    type Item = Arc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let data = self.clone().0 .0;

        *self = PersistentStackIter(PersistentStack(
            data.as_ref()
                .map(|x| x.parent.as_ref())
                .flatten()
                .map(|x| Arc::clone(x)),
        ));

        data.map(|x| Arc::clone(&x.data))
    }
}

impl<T> PersistentStack<T> {
    pub fn push(&mut self, data: T) {
        let node = PersistentStackNode {
            data: Arc::new(data),
            parent: self.0.as_ref().map(|x| Arc::clone(x)),
        };
        *self = PersistentStack(Some(Arc::new(node)));
    }
}
