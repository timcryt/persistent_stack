# Concurrent persistent stack

Fast, concurrent and easy to use implementation of persistent stack.

## Operations cost
- `push - O(1)`
- `pop  - O(1)`
- `clone - O(1)`
- `iter next - O(1)`

## Example

```rust
use persistent_stack::PersistentStack;

let mut s1 = PersistentStack::new();
s1.push(1);

let mut s2 = s1.clone(); // O(1) operation

std::thread::spawn(move || {
    s2.push(2); // PersistentStack values can be shared safely
    assert_eq!(s2.iter().copied().collect::<Vec<_>>(), vec![2, 1]);

    std::thread::sleep(std::time::Duration::from_millis(20));

    s2.push(4);
    assert_eq!(s2.iter().copied().collect::<Vec<_>>(), vec![4, 2, 1]);

    assert_eq!(s2.pop(), Ok(4)); // We can also pop values from stack
});

s1.push(3);
assert_eq!(s1.iter().copied().collect::<Vec<_>>(), vec![3, 1]);

std::thread::sleep(std::time::Duration::from_millis(20));

s1.push(5);
assert_eq!(s1.iter().copied().collect::<Vec<_>>(), vec![5, 3, 1]);
```