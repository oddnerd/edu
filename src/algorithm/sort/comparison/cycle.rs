//! Implementations of [Cycle Sort](https://en.wikipedia.org/wiki/Cycle_sort).

pub fn cycle<T: Ord + Clone>(elements: &mut [T]) {
    for start in 0..elements.len() {
        let mut item = elements[start].clone();

        let mut pos = start;

        for element in &elements[start + 1..] {
            if element < &item {
                pos += 1;
            }
        }

        if pos == start {
            continue;
        }

        while item == elements[pos] {
            pos += 1;
        }

        core::mem::swap(&mut elements[pos], &mut item);

        while pos != start {
            pos = start;

            for i in (start+1)..elements.len() {
                if elements[i] < item {
                    pos += 1;
                }
            }

            while item == elements[pos] {
                pos += 1;
            }

            core::mem::swap(&mut elements[pos], &mut item);
        }

    }

}
