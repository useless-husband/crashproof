/* Block-device primitives for the crashproof executable.
 * Lean's standard library cannot write at an offset or force data to stable storage,
 * so these five calls are the only C in the project. They are part of the trusted base. */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static lean_obj_res io_err(const char *what)
{
    char msg[256];
    snprintf(msg, sizeof msg, "%s: %s", what, strerror(errno));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res io_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

LEAN_EXPORT lean_obj_res crashproof_dev_open(b_lean_obj_arg path, uint8_t create)
{
    int fd = open(lean_string_cstr(path), O_RDWR | (create ? O_CREAT | O_TRUNC : 0), 0644);
    if (fd < 0) return io_err(lean_string_cstr(path));
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res crashproof_dev_close(uint32_t fd)
{
    if (close((int)fd) < 0) return io_err("close");
    return io_unit();
}

LEAN_EXPORT lean_obj_res crashproof_dev_size(uint32_t fd)
{
    struct stat st;
    if (fstat((int)fd, &st) < 0) return io_err("fstat");
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)st.st_size));
}

/* Reads past the end of the file return zeros. */
LEAN_EXPORT lean_obj_res crashproof_dev_pread(uint32_t fd, uint64_t off, size_t len)
{
    lean_object *arr = lean_alloc_sarray(1, len, len);
    uint8_t *p = lean_sarray_cptr(arr);
    size_t done = 0;
    while (done < len) {
        ssize_t r = pread((int)fd, p + done, len - done, (off_t)(off + done));
        if (r < 0) {
            if (errno == EINTR) continue;
            lean_dec(arr);
            return io_err("pread");
        }
        if (r == 0) {
            memset(p + done, 0, len - done);
            break;
        }
        done += (size_t)r;
    }
    return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res crashproof_dev_pwrite(uint32_t fd, uint64_t off, b_lean_obj_arg data)
{
    size_t len = lean_sarray_size(data);
    const uint8_t *p = lean_sarray_cptr(data);
    size_t done = 0;
    while (done < len) {
        ssize_t r = pwrite((int)fd, p + done, len - done, (off_t)(off + done));
        if (r < 0) {
            if (errno == EINTR) continue;
            return io_err("pwrite");
        }
        done += (size_t)r;
    }
    return io_unit();
}

/* The barrier. On macOS fsync() does not flush the drive's cache; F_FULLFSYNC does. */
LEAN_EXPORT lean_obj_res crashproof_dev_fsync(uint32_t fd)
{
#ifdef F_FULLFSYNC
    if (fcntl((int)fd, F_FULLFSYNC) == 0) return io_unit();
#endif
    if (fsync((int)fd) < 0) return io_err("fsync");
    return io_unit();
}

LEAN_EXPORT lean_obj_res crashproof_dev_usleep(uint32_t us)
{
    usleep(us);
    return io_unit();
}
