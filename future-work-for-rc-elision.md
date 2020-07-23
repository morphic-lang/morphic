# Future Work for RC Elision
- Allow heap structures to contain borrowed references to other heap structures (currently our design only allows for borrows on the stack)
- Avoid spurious post-mutation releases due to returning unused heap structures
