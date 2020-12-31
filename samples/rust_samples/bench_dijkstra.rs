struct Heap<T> {
    arr: Vec<T>,
}

impl<T: Ord> Heap<T> {
    fn empty() -> Heap<T> {
        Heap { arr: Vec::new() }
    }

    fn insert(&mut self, item: T) {
        self.arr.push(item);
        self.sift_up(self.arr.len() - 1);
    }

    fn remove(&mut self) -> Option<T> {
        if self.arr.len() > 0 {
            let i = self.arr.len() - 1;
            self.arr.swap(0, i);
            let root = self.arr.pop();
            self.sift_down(0);
            root
        } else {
            None
        }
    }

    fn sift_up(&mut self, i: usize) {
        let parent = ((i as isize - 1) / 2) as usize;
        if i != 0 && self.arr[parent] <= self.arr[i] {
            self.arr.swap(parent, i);
            self.sift_up(parent);
        }
    }

    fn sift_down(&mut self, i: usize) {
        let left_idx = 2 * i + 1;
        let right_idx = 2 * i + 2;

        let largest_left = if left_idx < self.arr.len() && self.arr[left_idx] > self.arr[i] {
            left_idx
        } else {
            i
        };

        let largest = if right_idx < self.arr.len() && self.arr[right_idx] > self.arr[largest_left]
        {
            right_idx
        } else {
            largest_left
        };

        if largest != i {
            self.arr.swap(largest, i);
            self.sift_down(largest);
        }
    }
}

fn main() {
    let mut heap = Heap::empty();
    heap.insert(8);
    heap.insert(7);
    heap.insert(6);
    heap.insert(9);
    heap.insert(3);
    heap.insert(1);
    heap.insert(5);
    heap.insert(2);
    heap.insert(0);
    heap.insert(4);
    heap.insert(10);

    while let Some(item) = heap.remove() {
        println!("{}", item);
    }
}
