# TODO List Of the Rust Filesystem Abstraction

- [x] Support for implementing multiple `inode::Operation` traits or `file::Operation` traits for a file system.
- [ ] Optimization of `ForeignOwnable` for `CString`, a new c string type, embedded length and capacity behind the pointer.
- [ ] Discussion on the design of `destroy_inode_callback`, does it need to treat all the `inode->i_link` as a `CString`? *Consider a small string embedded in the inode*.