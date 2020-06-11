/*
    y = x*r*pi * (1 - x) * r
    So x = 1/2
*/

fn transpose(dst: &mut [u64], src: &[u64], dim: usize) {
    // 2 x 4 blocking unrolling
    for i in (0..dim).step(2) {
        for j in (0..dim).step_by(4) {
            dst[j * dim + i]           = src[i * dim + j];
            dst[j * dim + i + dim]     = src[i * dim + j + 1];
            dst[j * dim + i + 2 * dim] = src[i + dim + j + 2];
            dst[j * dim + i + 3 * dim] = src[i + dim + j + 3];

            dst[j * dim + i + 1]           = src[i * dim + j + dim];
            dst[j * dim + i + dim + 1]     = src[i * dim + j + 1 + dim];
            dst[j * dim + i + 2 * dim + 1] = src[i + dim + j + 2 + dim];
            dst[j * dim + i + 3 * dim + 1] = src[i + dim + j + 3 + dim];
        }
    }
}

fn col_convert(G: &mut [u64], dim: usize) {
    // 4 x 1 unrolling with conditional check
    for i in (0..dim) {
        for j in (0..dim).step_by(4) {
            if G[i * dim + j] == 0 {
                G[i * dim + j]     = G[j * dim + i];
            }
            if G[i * dim + j + 1] == 0 {
                G[i * dim + j + 1] = G[j * dim + i + dim];
            }
            if G[i * dim + j + 2] == 0 {
                G[i * dim + j + 2] = G[j * dim + i + 2 * dim];
            }
            if G[i * dim + j + 3] == 0 {
                G[i * dim + j + 3] = G[j * dim + i + 3 * dim];
            }
        }
    }
}

