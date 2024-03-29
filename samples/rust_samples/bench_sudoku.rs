#![allow(dead_code)]

mod common {
    include!("common.rs");
}

use common::{read_line, repeat, write_report, Int, ProfileInfo};

static SOLVE_INFO: ProfileInfo = ProfileInfo::new();

fn rc_bp(r: Int, c: Int) -> (Int, Int) {
    (r / 3 * 3 + c / 3, (r % 3) * 3 + (c % 3))
}

fn bp_rc(r: Int, c: Int) -> (Int, Int) {
    rc_bp(r, c)
}

#[derive(Debug, Clone, Copy)]
struct Rule(Int);

enum RuleType {
    RC,
    RN,
    CN,
    BN,
}

impl Rule {
    const IS_SET: Int = 1 << 9;

    fn new() -> Self {
        Rule(Self::IS_SET - 1)
    }

    fn new_single(x: Int) -> Self {
        Rule((1 << x) | Self::IS_SET)
    }

    fn check_set(self) -> bool {
        (self.0 & Self::IS_SET) == Self::IS_SET
    }

    fn count_options(self) -> Int {
        (self.0 & !Self::IS_SET).count_ones() as Int
    }

    fn check_option(self, x: Int) -> bool {
        (self.0 & (1 << x)) != 0
    }

    fn set_false(&mut self, x: Int) {
        self.0 &= !(1 << x);
    }
}

#[derive(Debug, Clone)]
struct Sudoku {
    rules: Vec<Rule>,
}

fn id_to_type(id: Int) -> RuleType {
    match id / 81 {
        0 => RuleType::RC,
        1 => RuleType::RN,
        2 => RuleType::CN,
        3 => RuleType::BN,
        _ => panic!("invalid rule_id"),
    }
}

fn rule_to_id(t: RuleType, a: Int, b: Int) -> Int {
    (match t {
        RuleType::RC => 0,
        RuleType::RN => 81,
        RuleType::CN => 81 * 2,
        RuleType::BN => 81 * 3,
    }) + (9 * a + b)
}

fn rule_to_rcn(idx: Int, x: Int) -> (Int, Int, Int) {
    let t = id_to_type(idx);
    let a = idx % 81 / 9;
    let b = idx % 9;
    match t {
        RuleType::RC => (a, b, x),
        RuleType::RN => (a, x, b),
        RuleType::CN => (x, a, b),
        RuleType::BN => {
            let (r, c) = bp_rc(a, x);
            (r, c, b)
        }
    }
}

impl Sudoku {
    fn set_pencilmark_false(&mut self, r: Int, c: Int, n: Int) {
        let (b, p) = rc_bp(r, c);
        self.rules[rule_to_id(RuleType::RC, r, c) as usize].set_false(n);
        self.rules[rule_to_id(RuleType::RN, r, n) as usize].set_false(c);
        self.rules[rule_to_id(RuleType::CN, c, n) as usize].set_false(r);
        self.rules[rule_to_id(RuleType::BN, b, n) as usize].set_false(p);
    }

    fn set_pencilmark(&mut self, r: Int, c: Int, n: Int) {
        let (b, p) = rc_bp(r, c);
        for n2 in 0..9 {
            if n == n2 {
                self.rules[rule_to_id(RuleType::RC, r, c) as usize] = Rule::new_single(n);
            } else {
                self.set_pencilmark_false(r, c, n2);
            }
        }
        for c2 in 0..9 {
            if c == c2 {
                self.rules[rule_to_id(RuleType::RN, r, n) as usize] = Rule::new_single(c);
            } else {
                self.set_pencilmark_false(r, c2, n);
            }
        }
        for r2 in 0..9 {
            if r == r2 {
                self.rules[rule_to_id(RuleType::CN, c, n) as usize] = Rule::new_single(r);
            } else {
                self.set_pencilmark_false(r2, c, n);
            }
        }
        for p2 in 0..9 {
            if p == p2 {
                self.rules[rule_to_id(RuleType::BN, b, n) as usize] = Rule::new_single(p);
            } else {
                let (r2, c2) = bp_rc(b, p2);
                self.set_pencilmark_false(r2, c2, n);
            }
        }
    }

    fn new(givens: &str) -> Self {
        assert_eq!(givens.len(), 9 * 9, "input wrong size");
        let mut sudoku = Sudoku {
            rules: vec![Rule::new(); 9 * 9 * 4],
        };
        for (i, given) in givens.chars().enumerate() {
            if let Some(n) = given.to_digit(10) {
                assert_ne!(n, 0, "given cannot be 0");
                let r = i as Int / 9;
                let c = i as Int % 9;
                sudoku.set_pencilmark(r, c, n as Int - 1)
            }
        }
        sudoku
    }

    fn solve_rec(&self, solutions: &mut Vec<Sudoku>) {
        let rule_idx = self
            .rules
            .iter()
            .enumerate()
            .filter(|(_, rule)| !rule.check_set())
            .fold((10, None), |(min, min_opt), (idx, rule)| {
                let count = rule.count_options();
                if count < min {
                    (count, Some(idx))
                } else {
                    (min, min_opt)
                }
            });
        match rule_idx {
            (0, _) => {}
            (_, None) => {
                solutions.push(self.clone());
            }
            (_, Some(idx)) => {
                let rule = self.rules[idx];
                for x in 0..9 {
                    if rule.check_option(x) {
                        let (r, c, n) = rule_to_rcn(idx as Int, x);
                        let mut new_sudoku = self.clone();
                        new_sudoku.set_pencilmark(r, c, n);
                        new_sudoku.solve_rec(solutions);
                    }
                }
            }
        }
    }

    fn solve(&self) -> Vec<Sudoku> {
        SOLVE_INFO.record_call(|| {
            let mut solutions = Vec::new();
            self.solve_rec(&mut solutions);
            solutions
        })
    }
}

fn main() {
    // 546993 solutions
    let givens =
        ".......6..2.9..1....8..1..52..5..4....3..2....4......7.3..6.5....91.............."
            .to_string();

    match read_line().parse::<u64>() {
        Ok(iters) => {
            println!("Solving {} times", iters);
            let len = repeat(iters, || {
                let sudoku = Sudoku::new(&givens);
                let solutions = sudoku.solve();
                solutions.len()
            });
            if let Some(len) = len {
                println!("{len}");
                println!("should be 546993");
            }
        }

        _ => {
            eprintln!("Please enter an iteration count");
        }
    }

    write_report(&SOLVE_INFO);
}
