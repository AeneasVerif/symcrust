// Rather than roll out our own layer of memory management, we simply implement the `Allocator`
// trait, which integrates nicely with `Box<T>`, and avoids a lot of subtleties and pitfalls.
use std::alloc::*;

// Externals cannot take type parameters; the allocation functions return bytes, and we transmute
// then into the desired type.
extern {
    fn SymCryptCallbackAlloc(sz: usize) -> *mut u8;
    fn SymCryptCallbackFree(ptr: *mut u8);
}

pub struct Alloc;

impl Allocator for Alloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let sz = layout.size();
        let ptr: *mut u8 = unsafe { SymCryptCallbackAlloc(sz) };
        // Probably need to tweak SYMCRYPT_ASYM_ALIGN_VALUE accordingly.
        assert_eq!(ptr as usize % layout.align(), 0);
        if ptr == std::ptr::null_mut() {
            result::Error(AllocError)
        } else {
            result::Ok(std::ptr::NonNull::new_unchecked(ptr))
        }
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe {
            SymCryptCallbackFree(ptr as *mut u8)
        }
    }
}
