/* Host shim that drives wren-os's write-ahead log (kernel/log.c, compiled
 * unmodified) against a simulated asynchronous disk, with exactly the command
 * line of the crashproof executable, so harness/crashtest.py can test both.
 *
 * It supplies the handful of symbols log.c needs -- a buffer cache, the block
 * device, locks and sleep/wakeup -- as a single-threaded host model:
 *
 *   - a volatile array `vis[]` is what reads see (the OS page cache / driver);
 *   - `bwrite(b)` copies the buffer into `vis[]` and records a new pending
 *     version of that block; it does not touch the image file;
 *   - `blk_flush()` writes every block's current value to the image file and
 *     fsync()s -- the barrier -- then clears the pending versions;
 *   - a crash picks, for each block independently, the durable value or any
 *     pending version (optionally torn at a sector boundary), writes the
 *     result to the file and exits 99.
 *
 * That is the model of Crashproof.Disk, so if wren-os's protocol is correct
 * the same harness must accept its recovered images. The locks and
 * sleep/wakeup are no-ops: the harness runs one operation at a time.
 *
 * This file is MINE. kernel/log.c and lib/crc32c.c are compiled from the
 * wren-os repository as they are; see wren/README.md. */
#include "types.h"
#include "spinlock.h"
#include "bio.h"
#include "blk.h"
#include "stats.h"
#include "log.h"
#include <wren/fsformat.h>

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

/* ---- geometry: header at 0, log slots 1..64, data at 65.., descriptor last ---- */
#define NLOG (LOG_DATA_BLOCKS + 1)           /* 65 */
#define SB_MAGIC 0x42535043u                 /* "CPSB" */
static uint32_t g_ndata;
static uint32_t home_of(uint32_t a) { return NLOG + a; }
static uint32_t sb_block(void) { return NLOG + g_ndata; }
static uint32_t total_blocks(void) { return NLOG + g_ndata + 1; }
static uint32_t fs_size(void) { return NLOG + g_ndata; }

/* ---- simulated device state ---- */
static int img_fd = -1;
static uint8_t *vis;          /* current visible value per block (volatile) */
static bool *vis_loaded;      /* whether vis[b] has been filled from the file */
static uint8_t **pending;     /* pending[b] = concatenated versions since last flush */
static int *npending;         /* number of versions in pending[b] */
static uint32_t nblk;

/* crash configuration (mirrors the crashproof executable) */
static long cfg_crash_at = -1;
static uint64_t cfg_seed = 1;
static bool cfg_torn = false;
static bool cfg_fsync = true;
static long cfg_delay_us = 0;
static uint32_t *cfg_keep = NULL;
static int cfg_nkeep = -1;        /* -1 means random */
static long op_count = 0;

static uint64_t rng_state;
static uint64_t xrand(void) {
    uint64_t x = rng_state;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    rng_state = x;
    return (x * 0x2545F4914F6CDD1DULL) >> 11;
}
static uint32_t randn(uint32_t n) { return n ? (uint32_t)(xrand() % n) : 0; }

static void die(const char *m) { fprintf(stderr, "wrenlog: %s: %s\n", m, strerror(errno)); exit(1); }

static void file_read(uint32_t b, uint8_t *dst) {
    ssize_t r = pread(img_fd, dst, BSIZE, (off_t)b * BSIZE);
    if (r < 0) die("pread");
    if (r < BSIZE) memset(dst + r, 0, BSIZE - r);
}
static void file_write(uint32_t b, const uint8_t *src) {
    size_t done = 0;
    while (done < BSIZE) {
        ssize_t w = pwrite(img_fd, src + done, BSIZE - done, (off_t)b * BSIZE + done);
        if (w < 0) { if (errno == EINTR) continue; die("pwrite"); }
        done += (size_t)w;
    }
}
static uint8_t *vis_ptr(uint32_t b) {
    if (!vis_loaded[b]) { file_read(b, vis + (size_t)b * BSIZE); vis_loaded[b] = true; }
    return vis + (size_t)b * BSIZE;
}

/* a block that reached the platter after a power cut */
static void crash(void) {
    uint8_t durable[BSIZE], out[BSIZE];
    for (uint32_t b = 0; b < nblk; b++) {
        if (npending[b] == 0) continue;
        file_read(b, durable);
        if (cfg_nkeep >= 0) {                     /* directed: keep only listed blocks */
            bool keep = false;
            for (int i = 0; i < cfg_nkeep; i++) if (cfg_keep[i] == b) keep = true;
            if (keep) file_write(b, pending[b] + (size_t)(npending[b] - 1) * BSIZE);
            continue;
        }
        /* candidate values: durable, then every pending version */
        uint32_t ncand = (uint32_t)npending[b] + 1;
        uint32_t i = randn(ncand);
        const uint8_t *vi = (i == 0) ? durable : pending[b] + (size_t)(i - 1) * BSIZE;
        bool tear = cfg_torn && randn(3) == 0;
        if (tear) {
            uint32_t j = randn(ncand);
            const uint8_t *vj = (j == 0) ? durable : pending[b] + (size_t)(j - 1) * BSIZE;
            uint32_t k = 1 + randn(SECTORS_PER_BLOCK - 1);
            uint32_t cut = k * 512;
            memcpy(out, vi, cut);
            memcpy(out + cut, vj + cut, BSIZE - cut);
            file_write(b, out);
        } else if (i != 0) {
            file_write(b, vi);
        }
    }
    fprintf(stderr, "crash: power cut before block operation %ld\n", op_count);
    exit(99);
}

static void sim_step(void) {
    if (cfg_crash_at == op_count) crash();
    op_count++;
    if (cfg_delay_us > 0) usleep((useconds_t)cfg_delay_us);
}

static void push_pending(uint32_t b, const uint8_t *data) {
    pending[b] = realloc(pending[b], (size_t)(npending[b] + 1) * BSIZE);
    if (!pending[b]) die("realloc");
    memcpy(pending[b] + (size_t)npending[b] * BSIZE, data, BSIZE);
    npending[b]++;
}

/* ---- buffer cache (enough for the log: dedup by blockno, refcnt, pinning) ---- */
#define NBUF 256
static struct buf bufs[NBUF];
static uint8_t bufdata[NBUF][BSIZE];

struct buf *bread(uint32_t dev, uint32_t blockno) {
    struct buf *free_b = NULL;
    for (int i = 0; i < NBUF; i++) {
        if (bufs[i].refcnt > 0 && bufs[i].blockno == blockno && bufs[i].valid) {
            bufs[i].refcnt++;
            return &bufs[i];
        }
        if (!free_b && bufs[i].refcnt == 0) free_b = &bufs[i];
    }
    if (!free_b) { fprintf(stderr, "wrenlog: out of buffers\n"); exit(1); }
    free_b->dev = dev;
    free_b->blockno = blockno;
    free_b->refcnt = 1;
    free_b->valid = true;
    free_b->data = bufdata[free_b - bufs];
    memcpy(free_b->data, vis_ptr(blockno), BSIZE);
    return free_b;
}
void bwrite(struct buf *b) {
    memcpy(vis_ptr(b->blockno), b->data, BSIZE);
    push_pending(b->blockno, b->data);
    sim_step();
}
void brelse(struct buf *b) { if (b->refcnt > 0) b->refcnt--; }
void bpin(struct buf *b) { b->refcnt++; }
void bunpin(struct buf *b) { b->refcnt--; }

void blk_flush(void) {
    for (uint32_t b = 0; b < nblk; b++)
        if (npending[b] > 0) file_write(b, vis_ptr(b));
    if (cfg_fsync) {
#ifdef F_FULLFSYNC
        if (fcntl(img_fd, F_FULLFSYNC) != 0)
#endif
            if (fsync(img_fd) < 0) die("fsync");
    }
    for (uint32_t b = 0; b < nblk; b++) { free(pending[b]); pending[b] = NULL; npending[b] = 0; }
    sim_step();
}

/* ---- the stubs log.c links against ---- */
uint64_t kstats[NSTATS];
void spin_init(struct spinlock *lk, const char *n) { (void)lk; (void)n; }
void spin_lock(struct spinlock *lk) { (void)lk; }
void spin_unlock(struct spinlock *lk) { (void)lk; }
void proc_sleep(void *chan, struct spinlock *lk) { (void)chan; (void)lk;
    fprintf(stderr, "wrenlog: unexpected proc_sleep (should be single-threaded)\n"); exit(1); }
void proc_wakeup(void *chan) { (void)chan; }
int printk(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt); int r = vfprintf(stderr, fmt, ap); va_end(ap); return r;
}
void panic(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt); fprintf(stderr, "panic: "); vfprintf(stderr, fmt, ap);
    va_end(ap); fprintf(stderr, "\n"); exit(2);
}

/* ---- image setup, matching the crashproof format ---- */
static void dev_init(uint32_t ndata) {
    g_ndata = ndata;
    nblk = total_blocks();
    vis = calloc(nblk, BSIZE);
    vis_loaded = calloc(nblk, sizeof(bool));
    pending = calloc(nblk, sizeof(uint8_t *));
    npending = calloc(nblk, sizeof(int));
    if (!vis || !vis_loaded || !pending || !npending) die("calloc");
}

static uint32_t u32at(const uint8_t *b, int i) {
    return (uint32_t)b[i] | (uint32_t)b[i+1] << 8 | (uint32_t)b[i+2] << 16 | (uint32_t)b[i+3] << 24;
}
static void put_u32(uint8_t *b, int i, uint32_t v) {
    b[i] = v; b[i+1] = v >> 8; b[i+2] = v >> 16; b[i+3] = v >> 24;
}

/* tagged test block: same scheme as App.Image.tagBlock */
static void tag_block(uint32_t t, uint8_t *out) {
    if (t == 0) { memset(out, 0, BSIZE); return; }
    for (uint32_t i = 0; i < BSIZE; i++) {
        uint32_t s = i / 512, j = i % 512;
        if (j < 4) out[i] = (uint8_t)(t >> (8 * j));
        else if (j < 8) out[i] = (uint8_t)(s >> (8 * (j - 4)));
        else out[i] = (uint8_t)((t * 31 + i * 7) % 251);
    }
}
static void describe(const uint8_t *b, char *out) {
    uint32_t t = u32at(b, 0);
    uint8_t ref[BSIZE];
    tag_block(t, ref);
    if (memcmp(b, ref, BSIZE) == 0) { sprintf(out, "%u", t); return; }
    char *p = out; *p++ = '?';
    for (uint32_t s = 0; s < SECTORS_PER_BLOCK; s++)
        p += sprintf(p, "%s%u", s ? "," : "", u32at(b, s * 512));
}

static void open_image(const char *path, bool create, uint32_t ndata) {
    img_fd = open(path, O_RDWR | (create ? O_CREAT | O_TRUNC : 0), 0644);
    if (img_fd < 0) die(path);
    if (!create) {
        struct stat st; if (fstat(img_fd, &st) < 0) die("fstat");
        uint32_t nb = (uint32_t)(st.st_size / BSIZE);
        if (nb < 3) { fprintf(stderr, "wrenlog: image too small\n"); exit(1); }
        dev_init(nb - NLOG - 1);
        uint8_t sb[BSIZE]; file_read(sb_block(), sb);
        if (u32at(sb, 0) != SB_MAGIC) { fprintf(stderr, "wrenlog: not a crashproof image\n"); exit(1); }
        if (u32at(sb, 4) != LOG_DATA_BLOCKS) { fprintf(stderr, "wrenlog: log length is not %d\n", LOG_DATA_BLOCKS); exit(1); }
    } else {
        dev_init(ndata);
    }
    rng_state = cfg_seed * 0x9E3779B97F4A7C15ULL + 1;
}

static struct superblock make_sb(void) {
    struct superblock sb; memset(&sb, 0, sizeof sb);
    sb.magic = FS_MAGIC; sb.size = fs_size();
    sb.nlog = NLOG; sb.logstart = 0;
    return sb;
}

/* ---- commands ---- */
static int cmd_format(const char *path, uint32_t ndata) {
    if (ndata == 0 || ndata >= (1u << 31)) { fprintf(stderr, "bad --data\n"); return 1; }
    cfg_fsync = true;
    open_image(path, true, ndata);
    uint8_t zero[BSIZE]; memset(zero, 0, BSIZE);
    for (uint32_t b = 0; b < total_blocks(); b++) file_write(b, zero);  /* empty header = zeros */
    uint8_t sb[BSIZE]; memset(sb, 0, BSIZE);
    put_u32(sb, 0, SB_MAGIC); put_u32(sb, 4, LOG_DATA_BLOCKS); put_u32(sb, 8, ndata);
    file_write(sb_block(), sb);
    if (fsync(img_fd) < 0) die("fsync");
    return 0;
}

static int mount_dev(const char *path) {
    open_image(path, false, 0);
    struct superblock sb = make_sb();
    log_init(0, &sb);                  /* runs recovery */
    return 0;
}

static int cmd_recover(const char *path) {
    mount_dev(path);
    printf("recovered ops %ld\n", op_count);
    return 0;
}

static char *trim(char *s) {
    while (*s && isspace((unsigned char)*s)) s++;
    char *e = s + strlen(s);
    while (e > s && isspace((unsigned char)e[-1])) *--e = 0;
    return s;
}

static int cmd_run(const char *path, const char *wlpath) {
    mount_dev(path);
    FILE *f = fopen(wlpath, "r");
    if (!f) die(wlpath);
    char line[256];
    bool in_txn = false;
    long acks = 0;
    while (fgets(line, sizeof line, f)) {
        char *h = strchr(line, '#'); if (h) *h = 0;
        char *s = trim(line);
        if (!*s) continue;
        char cmd[32]; uint32_t a, t;
        if (strcmp(s, "begin") == 0) {
            if (in_txn) { fprintf(stderr, "begin inside a transaction\n"); return 1; }
            log_begin_op(); in_txn = true;
        } else if (sscanf(s, "%31s %u %u", cmd, &a, &t) == 3 && strcmp(cmd, "put") == 0) {
            if (!in_txn || a >= g_ndata) { fprintf(stderr, "bad put\n"); return 1; }
            struct buf *b = bread(0, home_of(a));
            tag_block(t, b->data);
            log_write(b);
            brelse(b);
        } else if (sscanf(s, "%31s %u %u", cmd, &a, &t) == 3 && strcmp(cmd, "get") == 0) {
            if (a >= g_ndata) { fprintf(stderr, "bad get\n"); return 1; }
            struct buf *b = bread(0, home_of(a));
            uint8_t ref[BSIZE]; tag_block(t, ref);
            if (memcmp(b->data, ref, BSIZE) != 0) {
                char d[512]; describe(b->data, d);
                printf("read-mismatch %u: expected %u, got %s\n", a, t, d);
                fflush(stdout); brelse(b); return 3;
            }
            brelse(b);
        } else if (strcmp(s, "commit") == 0) {
            if (!in_txn) { fprintf(stderr, "commit outside a transaction\n"); return 1; }
            log_end_op(); in_txn = false;
            acks++; printf("ack %ld\n", acks); fflush(stdout);
        } else {
            fprintf(stderr, "bad workload line: %s\n", s); return 1;
        }
    }
    fclose(f);
    printf("ops %ld\n", op_count);
    return 0;
}

static int cmd_dump(const char *path) {
    open_image(path, false, 0);
    uint8_t h[BSIZE]; file_read(0, h);
    struct log_header hdr; memcpy(&hdr, h, sizeof hdr);
    if (hdr.magic != LOG_MAGIC || hdr.n == 0) printf("header empty\n");
    else {
        printf("header commits %u blocks [", hdr.n);
        for (uint32_t i = 0; i < hdr.n && i < LOG_DATA_BLOCKS; i++)
            printf("%s%u", i ? ", " : "", hdr.block[i] - NLOG);  /* logical address */
        printf("]\n");
    }
    for (uint32_t a = 0; a < g_ndata; a++) {
        uint8_t b[BSIZE]; file_read(home_of(a), b);
        char d[512]; describe(b, d);
        printf("%u %s\n", a, d);
    }
    return 0;
}

static void parse_device_flags(int argc, char **argv, int start) {
    for (int i = start; i < argc; i++) {
        if (strcmp(argv[i], "--crash-at") == 0 && i + 1 < argc) cfg_crash_at = atol(argv[++i]);
        else if (strcmp(argv[i], "--seed") == 0 && i + 1 < argc) cfg_seed = strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--torn") == 0) cfg_torn = true;
        else if (strcmp(argv[i], "--no-fsync") == 0) cfg_fsync = false;
        else if (strcmp(argv[i], "--delay-us") == 0 && i + 1 < argc) cfg_delay_us = atol(argv[++i]);
        else if (strcmp(argv[i], "--keep") == 0 && i + 1 < argc) {
            char *l = argv[++i]; cfg_nkeep = 0; cfg_keep = calloc(64, sizeof(uint32_t));
            for (char *tok = strtok(l, ","); tok && cfg_nkeep < 64; tok = strtok(NULL, ","))
                cfg_keep[cfg_nkeep++] = (uint32_t)atol(tok);
        } else { fprintf(stderr, "unknown flag %s\n", argv[i]); exit(1); }
    }
}

int main(int argc, char **argv) {
    if (argc >= 3 && strcmp(argv[1], "format") == 0) {
        uint32_t ndata = 32;
        for (int i = 3; i < argc; i++) {
            if (strcmp(argv[i], "--data") == 0 && i + 1 < argc) ndata = (uint32_t)atol(argv[++i]);
            else if (strcmp(argv[i], "--log") == 0 && i + 1 < argc) {
                if (atol(argv[++i]) != LOG_DATA_BLOCKS) {
                    fprintf(stderr, "wrenlog: --log must be %d (wren-os fixes it)\n", LOG_DATA_BLOCKS);
                    return 1;
                }
            } else { fprintf(stderr, "unknown flag %s\n", argv[i]); return 1; }
        }
        return cmd_format(argv[2], ndata);
    }
    if (argc >= 3 && strcmp(argv[1], "recover") == 0) {
        parse_device_flags(argc, argv, 3);
        return cmd_recover(argv[2]);
    }
    if (argc >= 4 && strcmp(argv[1], "run") == 0) {
        parse_device_flags(argc, argv, 4);
        return cmd_run(argv[2], argv[3]);
    }
    if (argc == 3 && strcmp(argv[1], "dump") == 0) return cmd_dump(argv[2]);
    fprintf(stderr, "usage: wrenlog format|recover|run|dump IMAGE ...\n");
    return 1;
}
