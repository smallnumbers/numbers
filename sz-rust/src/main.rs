use std::env;
use std::time::Instant;

struct SzContext {
    n : usize,
    k : usize,

    // Existing Szemereti numbers, sz[n'][k'].
    sz : Vec<Vec<usize>>,

    // Data structures used during recursion.
    stack : Vec<usize>,
    result_space : Vec<usize>,
    size_to_beat : usize,

}

fn propagate(ctx : &SzContext,
             a : usize, h: usize) -> Result<usize, usize>
{
    if ctx.sz[ctx.n - a][ctx.k] > 0 &&
       h + 1 + ctx.sz[ctx.n - a][ctx.k] < ctx.size_to_beat
    {
        return Err(0);
    }

    let mut d: usize = 1;

    while d <= (a + 1) / (ctx.k - 1)
    {
        let mut all_in : usize = 1;
        let mut j : usize = 1;

        while all_in > 0 && j < ctx.k && (j * d) <= a
        {
            all_in = ctx.stack[a - j * d];
            j = j + 1;
        }

        if all_in > 0 && j == ctx.k
        {
            return Err(0);
        }

        d = d + 1;
    }

    return Ok(1);
}

fn compute_sz_recurse(mut ctx : SzContext,
                      mut a : usize, h : usize) -> Result<SzContext, usize>
{
    if h >= ctx.n {
        println!("BUG: recursion height is too large!");
        return Err(0);
    }

    if a >= ctx.n {
        if h > ctx.size_to_beat {
            let mut i : usize = 0;
            while i < ctx.n {
                ctx.result_space[i] = ctx.stack[i];
                i = i + 1;
            }
            ctx.size_to_beat = h;
        }
        return Ok(ctx);
    }

    while a < ctx.n {
        let mut i: usize = a;

        while i < ctx.n {
            ctx.stack[i] = 0;
            i = i + 1;
        }

        // Add element 'a' to the set.
        ctx.stack[a] = 1;

        let pres = propagate(&ctx, a, h);

        if pres.is_ok() {
            if ctx.size_to_beat < h + 1 {
                let mut i : usize = 0;
                while i < ctx.n {
                    ctx.result_space[i] = ctx.stack[i];
                    i = i + 1;
                }
                ctx.size_to_beat = h + 1;
            }

            ctx = compute_sz_recurse(ctx, a + 1, h + 1).expect("failed during recursion");
        }
        ctx.stack[a] = 0;

        a = a + 1;
    }

    return Ok(ctx);
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let min_n : usize = args[1].parse::<usize>().unwrap();
    let max_n : usize = args[2].parse::<usize>().unwrap();
    let max_k : usize = args[3].parse::<usize>().unwrap();

    println!("min_n: {}, max_n: {}, max_k: {}", min_n, max_n, max_k);

    let mut ctx : SzContext = SzContext {
        n : min_n,
        k : 3,
        sz: Vec::with_capacity(max_n + 1),
        stack: Vec::with_capacity((max_n + 1) * (max_n + 1)),
        result_space: Vec::with_capacity(max_n + 1),
        size_to_beat: 0,
    };

    let mut i : usize = 0;

    while i <= max_n {
        ctx.sz.push(Vec::with_capacity(max_n + 1));
        ctx.result_space.push(0);

        let mut j : usize = 0;

        while j < max_n {
            ctx.stack.push(0);
            ctx.sz[i].push(0);

            j = j + 1;
        }

        i = i + 1;
    }

    let mut n : usize = min_n;

    while n <= max_n {
        let mut k = 3;

        while k <= max_k {
            let mut i : usize = 0;

            while i <= max_n * max_n {
                ctx.stack[i] = 0;
                i = i + 1;
            }

            ctx.n = n;
            ctx.k = k;
            ctx.size_to_beat = 0;

            let before = Instant::now();
            ctx = compute_sz_recurse(ctx, 0, 0).expect("failed during recursion");
            let after = Instant::now();

            ctx.sz[n][k] = ctx.size_to_beat;

            print!("sz({},{})={}\t", n, k, ctx.size_to_beat);
            let mut i : usize = 0;
            while i < n {
                print!("{}", ctx.result_space[i]);
                i = i + 1;
            }
            println!("\tfinished in {} ms", after.duration_since(before).as_millis());

            k = k + 1;
        }

        n = n + 1;
    }

}
