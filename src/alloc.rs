// Rather than roll out our own layer of memory management, we simply implement the `Allocator`
// trait, which integrates nicely with `Box<T>`, and avoids a lot of subtleties and pitfalls.
//
// The Allocator trait is intended for more low-level allocators, which have a notion of allocation
// size (which may be larger than the requested size). The API for client-provided allocators in
// SymCrypt does not capture this level of detail, meaning that we do not do anything smart and
// always assume that the allocation returned by SymCryptCallbackAlloc is always of exactly the
// right size (even though it may be larger under the hood).
use std::alloc::*;
use std::ptr::NonNull;
use std::result::Result;

extern {
    fn SymCryptCallbackAlloc(sz: usize) -> *mut u8;
    fn SymCryptCallbackFree(ptr: *mut u8);
}

pub struct Alloc;

unsafe impl Allocator for Alloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let sz = layout.size();
        let ptr: *mut u8 = unsafe { SymCryptCallbackAlloc(sz) };
        // TODO: determine what may be the maximum alignment requested by Rust (perhaps 8 bytes?)
        // and set SYMCRYPT_ASYM_ALIGN_VALUE accordingly so that the allocation below always
        // succeeds.
        assert_eq!(ptr as usize % layout.align(), 0);
        if ptr.is_null() {
            Result::Err(AllocError)
        } else {
            unsafe {
                // TODO: determine if this is the best way to create a slice from a raw C pointer
                let s: &mut[u8] = std::slice::from_raw_parts_mut(ptr, layout.size());
                Result::Ok(NonNull::new_unchecked(s as *mut[u8]))
            }
        }
    }

    unsafe fn deallocate(&self, mut ptr: NonNull<u8>, _layout: Layout) {
        unsafe {
            SymCryptCallbackFree(ptr.as_mut())
        }
    }
}
