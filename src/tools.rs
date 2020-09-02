pub mod tools {
    use std::collections::{HashMap, HashSet};
    use std::collections::hash_map::RandomState;
    use std::fmt::{Display};
    use std::hash::Hash;

// fn combinations<'a, T: 'a, I: Iterator<Item = &'a T> + Clone>(mut sets: impl Iterator<Item = I>) -> impl Iterator<Item = Vec<&'a T>> {
//     let first = sets.next();
//     let second = sets.next();
//     if first.is_none() || second.is_none() {
//         return iter::empty();
//     }
//
//     let initial = Itertools::cartesian_product(first.unwrap(), second.unwrap())
//         .map(|p| vec![p.0, p.1]);
//     let res = sets.fold(initial, |res, i| Itertools::cartesian_product(res, i));
//     res.unwrap_or(iter::empty())
// }

    // TODO: don't clone T to satisfy borrow checker
    pub(crate) fn combinations<T: Clone>(sets: &[&HashSet<T>]) -> Vec<Vec<T>> {
        if sets.is_empty() {
            return Vec::new();
        }
        if sets.len() == 1 {
            return sets[0].iter().map(|t| vec![t.clone()]).collect();
        }

        let rec_res = combinations(&sets[1..sets.len()]);
        // TODO: clone iterator
        let initial_set = &sets[0];
        let mut res = Vec::new();
        for s in initial_set.iter() {
            for r in rec_res.iter() {
                let mut new_r = r.clone();
                new_r.push(s.clone());
                res.push(new_r)
            }
        }

        return res;
    }

    pub fn choose<K>(vec: &[K], size: usize) -> Vec<Vec<&K>> {
        if size == 1 {
            let mut res = Vec::default();
            vec.iter().for_each(|k| res.push(vec![k.clone()]));
            return res;
        }
        if size == 0 || size > vec.len() {
            return Vec::default();
        }

        let mut res = Vec::default();
        for (i, k) in vec.iter().enumerate() {
            let mut rec_res = choose(&vec[i + 1..], size - 1);
            for v in rec_res.iter_mut() {
                v.push(k);
            }
            res.extend(rec_res);
        }
        res
    }

    pub trait Grouped<T> {
        fn grouped<K: Hash + Eq, F: Fn(&T) -> K>(&mut self, key: F) -> HashMap<K, Vec<T>>;
    }

    impl<T, I: Iterator<Item = T>> Grouped<T> for I {
        fn grouped<K: Hash + Eq, F: Fn(&T) -> K>(&mut self, key: F) -> HashMap<K, Vec<T>, RandomState> {
            let mut res = HashMap::new();
            self.for_each(|t| res.entry(key(&t)).or_insert(Vec::new()).push(t));
            res
        }
    }

    pub fn print_iter<T: Display, I: Iterator<Item = T>>(x: I) {
        for y in x {
            print!("{}, ", y);
        }
        println!();
    }

    // pub trait DispWrapper {
    //     fn to_print_str(&self) -> String;
    // }
    //
    // impl<T: ToString> DispWrapper for T {
    //     fn to_print_str(&self) -> String {
    //         self.to_string()
    //     }
    // }
    //
    // impl<T: DispWrapper, I: Iterator<Item = T> + Clone> DispWrapper for I {
    //     fn to_print_str(&self) -> String {
    //         let mut res = String::new();
    //         let mut cloned = self.clone();
    //         let mut next = cloned.next();
    //         while next.is_some() {
    //             res += &*next.as_ref().unwrap().to_print_str();
    //             res += ", "
    //         }
    //         res
    //     }
    // }
    //
    // impl<T: DispWrapper> Display for T {
    //     fn fmt(&self, f: &mut Formatter<'_>) -> Result {
    //         self.to_print_str().fmt(f)
    //     }
    // }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::iter::FromIterator;

    use crate::tools::tools::choose;
    use crate::tools::tools::combinations;

    #[test]
    fn check_comb_amount() {
        let v1 = vec![1, 2, 3];
        let v2 = vec![4, 5, 6];
        let sets = vec![v1.iter().collect::<HashSet<&i32>>(), v2.iter().collect::<HashSet<&i32>>()];
        let combs = combinations(&sets.iter().collect::<Vec<&HashSet<&i32>>>());
        assert_eq!(combs.len(), 9);
        for v in &combs {
            assert_eq!(v.len(), 2);
        }
        // No doubles
        let as_set: HashSet<&Vec<&i32>> = HashSet::from_iter(combs.iter());
        assert_eq!(as_set.len(), 9);
    }

    #[test]
    fn check_choose_amount() {
        let v3 = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
        for i in 1..9 {
            let chosen = choose(&v3, i);
            for v in &chosen {
                assert_eq!(v.len(), i);
            }
            let as_set: HashSet<&Vec<&i32>> = HashSet::from_iter(chosen.iter());
            assert_eq!(chosen.len(), as_set.len());
        }
    }
}