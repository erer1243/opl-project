use std::convert::From;
use std::fmt::Debug;
use std::iter::FromIterator;
use std::ops::Deref;

// A "smart" pointer that leaks the memory of whatever it allocates
pub struct Leak<T>(*mut T);

impl<T> Leak<T> {
    pub fn new(data: T) -> Self {
        Leak(Box::into_raw(Box::new(data)))
    }

    pub fn set(&self, data: T) {
        unsafe {
            *self.0 = data;
        }
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

impl<T: PartialEq> PartialEq<Leak<T>> for Leak<T> {
    fn eq(&self, other: &Leak<T>) -> bool {
        self.deref().eq(other)
    }
}

impl<T: Eq> Eq for Leak<T> {}

// Linked list built with the Leak type
#[derive(PartialEq, Eq)]
pub struct List<T>(Link<T>);

type Link<T> = Option<Leak<Node<T>>>;

#[derive(PartialEq, Eq)]
struct Node<T> {
    data: T,
    next: Link<T>,
}

// Convenience alias to make List::cons into just cons
pub fn cons<T>(data: T, tail: List<T>) -> List<T> {
    List::cons(data, tail)
}

impl<T> List<T> {
    pub const fn new() -> Self {
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

    pub fn head(&self) -> Option<&T> {
        self.head_tail().map(|(t, _)| t)
    }

    pub fn is_empty(self) -> bool {
        self.0.is_none()
    }

    pub fn len(mut self) -> usize {
        let mut n = 0;
        while let Some((_, next)) = self.head_tail() {
            n += 1;
            self = next;
        }
        n
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

    // Panics if called on empty list
    pub fn last(self) -> T {
        // Only will ever use this with free-to-clone types
        self.to_vec().last().unwrap().clone()
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

impl<I: IntoIterator> From<I> for List<I::Item> {
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
// pub trait IntoList<T>: Into<List<T>> {}
// impl<T, S> IntoList<T> for S where S: Into<List<T>> {}

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

    let l1 = List::from([1, 2, 3]);
    let l2 = List::from([1, 2, 3]);
    let l3 = List::from([1, 2, 3, 4]);
    assert_eq!(l1, l1);
    assert_eq!(l1, l2);
    assert_ne!(l1, l3);
}

#[test]
fn leak_eq_test() {
    assert_eq!(Leak::new(5), Leak::new(5));
    assert_ne!(Leak::new(5), Leak::new(6));
    let five = Leak::new(5);
    assert_eq!(five, five);
}
