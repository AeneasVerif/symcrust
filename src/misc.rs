// Demo-ing the allocation strategy of temporaries.
struct Temporaries {
    data1: [u8; 16],
    data2: [u8; 16],
}

fn do_work<'a, F: FnOnce() -> &'a mut Temporaries>(alloc: F) -> u8 {
    let tmp = alloc();
    let Temporaries { ref mut data1, ref mut data2 } = tmp;
    data1[0] = data1[0] + data2[0] + 1;
    data1[0]
}

fn main() {
    let mut tmp = Temporaries { data1: [0; 16], data2: [0; 16] };
    let r = do_work(|| { &mut tmp });
    let mut tmp2 = Box::new(Temporaries { data1: [0; 16], data2: [0; 16] });
    let r = do_work(|| { &mut tmp2 });
    assert_eq!(r, 1);
}
