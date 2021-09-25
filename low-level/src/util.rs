use std::convert::From;
use std::fmt::Debug;
use std::iter::FromIterator;
use std::ops::Deref;

// A "smart" pointer that leaks the memory of whatever it allocates
pub struct Leak<T>(*const T);

impl<T> Leak<T> {
    pub fn new(data: T) -> Self {
        Leak(Box::into_raw(Box::new(data)))
    }
}

impl<T> Clone for Leak<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Leak<T> {}

impl<T> Deref for Leak<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.0 }
    }
}

impl<T: Debug> Debug for Leak<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

// Linked list built with the Leak type
pub struct List<T>(Link<T>);

type Link<T> = Option<Leak<Node<T>>>;

struct Node<T> {
    data: T,
    next: Link<T>,
}

// Convenience alias to make List::cons into just cons
pub fn cons<T>(data: T, tail: List<T>) -> List<T> {
    List::cons(data, tail)
}

impl<T> List<T> {
    pub fn new() -> Self {
        List(None)
    }

    pub fn cons(data: T, tail: List<T>) -> List<T> {
        let node = Node { data, next: tail.0 };

        List(Some(Leak::new(node)))
    }

    pub fn head_tail(&self) -> Option<(&T, List<T>)> {
        match &self.0 {
            Some(node) => Some((&node.data, List(node.next))),
            None => None,
        }
    }

    pub fn is_empty(self) -> bool {
        self.0.is_none()
    }
}

// Allow cloning list into vec for a few inconvenient spots
// Of course this is never necessary, just makes some code easier
// that could be improved in the future for enhanced performance
impl<T: Clone> List<T> {
    pub fn to_vec(self) -> Vec<T> {
        let mut vec = Vec::new();

        let mut curr = self.0;
        while let Some(node) = curr {
            vec.push(node.data.clone());
            curr = node.next;
        }

        vec
    }
}

impl<T> Clone for List<T> {
    fn clone(&self) -> Self {
        List(self.0)
    }
}

impl<T> Copy for List<T> {}

impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        // Lazy implementation, allocates a vector to reverse the elements
        let mut vec: Vec<T> = iter.into_iter().collect();
        vec.reverse();

        let mut list = List::new();
        for itm in vec {
            list = cons(itm, list);
        }
        list
    }
}

impl<T, I: IntoIterator<Item = T>> From<I> for List<T> {
    fn from(iter: I) -> Self {
        List::from_iter(iter)
    }
}

impl<T: Debug + Clone> Debug for List<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.to_vec())
    }
}

// Alias trait for Into<List<T>> -> IntoList<T>
pub trait IntoList<T>: Into<List<T>> {}
impl<T, S> IntoList<T> for S where S: Into<List<T>> {}

#[test]
fn linked_list_test() {
    assert!(List::<()>::new().is_empty());
    assert!(!List::from([1, 2, 3]).is_empty());

    assert!(List::<()>::new().head_tail().is_none());

    let list = List::from([1, 2, 3]);

    let (h0, tail) = list.head_tail().unwrap();
    let (h1, tail) = tail.head_tail().unwrap();
    let (h2, tail) = tail.head_tail().unwrap();
    assert!(tail.head_tail().is_none());

    assert_eq!(*h0, 1);
    assert_eq!(*h1, 2);
    assert_eq!(*h2, 3);
}
