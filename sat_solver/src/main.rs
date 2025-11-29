use std::io::{self, Read};

type Lit = i32;
type Clause = Vec<Lit>;

struct Solver {
    clauses: Vec<Clause>,
    num_vars: usize,
    assignment: Vec<Option<bool>>,
    history: Vec<Lit>,
    positives: Vec<usize>,
    negatives: Vec<usize>,
    literal_polarity: Vec<i8>,
    watches: Vec<(usize, usize)>,
    watch_lists: Vec<Vec<usize>>,
}

impl Solver {
    fn new(clauses: Vec<Clause>, num_vars: usize) -> Self {
        let mut solver = Solver {
            clauses,
            num_vars,
            assignment: vec![None; num_vars + 1],
            history: Vec::with_capacity(num_vars + 1),
            positives: vec![0; num_vars + 1],
            negatives: vec![0; num_vars + 1],
            literal_polarity: vec![0; num_vars + 1],
            watches: Vec::new(),
            watch_lists: vec![Vec::new(); 2 * (num_vars + 1)],
        };
        solver.preprocess();
        solver
    }

    fn lit_index(&self, lit: Lit) -> usize {
        if lit > 0 {
            (lit as usize) * 2
        } else {
            ((-lit) as usize) * 2 + 1
        }
    }

    fn preprocess(&mut self) {
        self.clauses.retain(|clause| {
            for i in 0..clause.len() {
                for j in (i + 1)..clause.len() {
                    if clause[i] == -clause[j] {
                        return false;
                    }
                }
            }
            true
        });
        
        // So we are checking shortest clauses first, exploring variables that affect the first clauses. Optimization
        self.clauses.sort_by_key(|c| c.len());

        
        self.watches = vec![(0, 1); self.clauses.len()];
        // two-watched literals
        for (idx, clause) in self.clauses.iter().enumerate() {
            if clause.is_empty() {
                continue;
            }

            let lit_idx = self.lit_index(clause[0]);
            self.watch_lists[lit_idx].push(idx);

            if clause.len() > 1 {
                let lit_idx2 = self.lit_index(clause[1]);
                self.watch_lists[lit_idx2].push(idx);
            }
        }


        // Pure literal optimization 
        for clause in &self.clauses {
            for &lit in clause {
                let var = lit.abs() as usize;
                if lit > 0 {
                    self.positives[var] += 1;
                } else {
                    self.negatives[var] += 1;
                }
            }
        }

        for v in 1..=self.num_vars {
            if self.positives[v] > 0 && self.negatives[v] == 0 {
                self.literal_polarity[v] = 1;
            } else if self.negatives[v] > 0 && self.positives[v] == 0 {
                self.literal_polarity[v] = -1;
            }
        }

    }
    
    #[inline(always)]
    fn val(&self, lit: Lit) -> Option<bool> {
        let var_idx = lit.abs() as usize;
        match self.assignment[var_idx] {
            Some(val) => {
                if lit > 0 { 
                    Some(val) 
                } else { 
                    Some(!val) 
                }
            }
            None => None,
        }
    }
    
    #[warn(dead_code)]
    fn pick_variable_two(&self) -> usize {
        let mut best_var = 0;
        let mut best_score = 0;
        
        for v in 1..=self.num_vars {
            if self.assignment[v].is_none() {
                let score = self.positives[v] + self.negatives[v];
                if score > best_score {
                    best_score = score;
                    best_var = v;
                }
            }
        }
        
        best_var
    }
    
    fn pick_variable(&self) -> usize {
        // heuristic picking variable appearing in most unresolved clauses
        let mut scores = vec![0; self.num_vars + 1];
        for clause in &self.clauses {
            let mut satisfied = false;
            for &lit in clause {
                if let Some(true) = self.val(lit) {
                    satisfied = true;
                    break;
                }
            }
            if !satisfied {
                for &lit in clause {
                    let var = lit.abs() as usize;
                    if self.assignment[var].is_none() {
                        scores[var] += 1;
                    }
                }
            }
        }
        

        let mut best_var = 0;
        let mut best_score = 0;

        for v in 1..=self.num_vars {
            if self.assignment[v].is_none() && scores[v] > best_score {
                best_score = scores[v];
                best_var = v;
            }
        }

        best_var
    }



    fn solve(&mut self) -> bool {
        // Unit propagation
        let entry_snapshot = self.history.len();
        
        if entry_snapshot == 0 {
            for v in 1..=self.num_vars {
                if self.assignment[v].is_none() && self.literal_polarity[v] != 0 {
                    let lit = if self.literal_polarity[v] > 0 {
                        v as i32
                    } else {
                        -(v as i32)
                    };
                    if !self.propagate(lit) {
                        self.backtrack(entry_snapshot);
                        return false;
                    }
                    self.assign_lit(lit);
                }
            }
        }
        
        if !self.bcp() {
            self.backtrack(entry_snapshot);
            return false;
        }

        let pick_var = self.pick_variable();

        // Could not find an unassigned variable and therefore must be true
        if pick_var == 0 {
            return true;
        }

        let try_positive_first = self.positives[pick_var] >= self.negatives[pick_var];

        let snapshot = self.history.len();
        
        let first_lit = if try_positive_first {
            pick_var as i32
        } else {
            -(pick_var as i32)
        };

        if self.propagate(first_lit) && self.solve() {
            return true;
        }

        self.backtrack(snapshot);
        
        if self.propagate(-first_lit) && self.solve() {
            return true;
        }

        self.backtrack(entry_snapshot);
        false
    }

    fn bcp(&mut self) -> bool {
        let mut changed = true;

        while changed {
            changed = false;

            for clause_idx in 0..self.clauses.len() {
                let clause = &self.clauses[clause_idx];
                
                let mut unassigned_count = 0;
                let mut last_unassigned = 0;

                for &lit in clause {
                    match self.val(lit) {
                        Some(true) => {
                            unassigned_count = 2;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unassigned_count += 1;
                            last_unassigned = lit;
                            if unassigned_count > 1 {
                                break;
                            }
                        }
                    }
                }

                if unassigned_count == 0 {
                    return false;
                }

                if unassigned_count == 1 {
                    if self.val(last_unassigned).is_none() {
                        if !self.propagate(last_unassigned) {
                            return false;
                        }
                        changed = true;
                    }
                }
            }
        }
        true
    }

    fn propagate(&mut self, lit: Lit) -> bool {
        if let Some(val) = self.val(lit) {
            return val;
        }

        self.assign_lit(lit);

        let neg_lit = -lit;
        let neg_idx = self.lit_index(neg_lit);

        let mut i = 0;
        while i < self.watch_lists[neg_idx].len() {
            let clause_idx = self.watch_lists[neg_idx][i];
            let clause = &self.clauses[clause_idx];

            let (first, second) = self.watches[clause_idx];

            let (current, other) = if clause[first] == neg_lit {
                (first, second)
            } else {
                (second, first)
            };

            if let Some(true) = self.val(clause[other]) {
                i += 1;
                continue;
            }

            let mut found_new_watch = false;
            for j in 2..clause.len() {
                if j == current || j == other {
                    continue;
                }
                if self.val(clause[j]) != Some(false) {
                    let new_idx = self.lit_index(clause[j]);
                    if current == first {
                        self.watches[clause_idx] = (j, second);
                    } else {
                        self.watches[clause_idx] = (first, j);
                    }
                    self.watch_lists[neg_idx].swap_remove(i);
                    self.watch_lists[new_idx].push(clause_idx);
    
                    found_new_watch = true;
                    break;
                }

            }
            if !found_new_watch {
                i += 1;
            }
        }   
        true
    }
 
    fn backtrack(&mut self, saved_len: usize) {
        while self.history.len() > saved_len {
            let lit = self.history.pop().unwrap();
            let var_idx = lit.abs() as usize;
            self.assignment[var_idx] = None;
        }
    }

    #[inline(always)]
    fn assign_lit(&mut self, lit: Lit) {
        let var_idx = lit.abs() as usize;
        if self.assignment[var_idx].is_none() {
            let val = lit > 0;
            self.assignment[var_idx] = Some(val);
            self.history.push(lit);
        }
    }

}


fn main() {
    let stdin = io::stdin();
    let mut handle = stdin.lock();
    let mut buffer = String::new();

    handle.read_to_string(&mut buffer).unwrap();

    let mut clauses: Vec<Clause> = Vec::new();
    let mut num_vars = 0;

    let mut current_clause: Clause = Vec::new();

    for line in buffer.lines() {
        let l = line.trim();
        if l.is_empty() || l.starts_with("c") { continue; }
        if l.starts_with("p") {
            let parts: Vec<&str> = l.split_whitespace().collect();
            num_vars = parts[2].parse().unwrap();
            continue;
        }

        let nums: Vec<i32> = l.split_whitespace()
            .map(|x| x.parse().unwrap())
            .collect();
        
        for n in nums {
            if n == 0 {
                if !current_clause.is_empty() {
                    clauses.push(current_clause.clone());
                    current_clause.clear();
                }
            }
            else {
                current_clause.push(n);
            }
        } 
    }


    let mut solver = Solver::new(clauses, num_vars);

    if solver.solve() {
        println!("SATISFIABLE");
        for i in 1..=num_vars {
            let lit = i as i32;
            match solver.val(lit) {
                Some(true) => print!(" {}", i),
                Some(false) => print!(" -{}", i),
                None => print!(" {}", i),
            }
        }
        println!();
    } else {
        println!("UNSATISFIABLE")
    }
    
    
}
