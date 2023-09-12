/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*      KC Sivaramakrishnan, Indian Institute of Technology, Madras       */
/*                   Stephen Dolan, University of Cambridge               */
/*                                                                        */
/*   Copyright 2016 Indian Institute of Technology, Madras                */
/*   Copyright 2016 University of Cambridge                               */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/
#define CAML_INTERNALS

#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <sys/time.h>
#include "caml/osdeps.h"
#include "caml/platform.h"
#include "caml/fail.h"
#include "caml/lf_skiplist.h"
#ifdef HAS_SYS_MMAN_H
#include <sys/mman.h>
#endif
#ifdef _WIN32
#include <windows.h>
#endif
#ifdef DEBUG
#include "caml/domain.h"
#endif

/* Error reporting */

void caml_plat_fatal_error(const char * action, int err)
{
  char buf[1024];
  caml_fatal_error("Fatal error during %s: %s\n",
                   action, caml_strerror(err, buf, sizeof(buf)));
}

/* Mutexes */

void caml_plat_mutex_init(caml_plat_mutex * m)
{
  int rc;
  pthread_mutexattr_t attr;
  rc = pthread_mutexattr_init(&attr);
  if (rc != 0) goto error1;
  rc = pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_ERRORCHECK);
  if (rc != 0) goto error2;
  rc = pthread_mutex_init(m, &attr);
  // fall through
error2:
  pthread_mutexattr_destroy(&attr);
error1:
  check_err("mutex_init", rc);
}

void caml_plat_assert_locked(caml_plat_mutex* m)
{
#ifdef DEBUG
  int r = pthread_mutex_trylock(m);
  if (r == EBUSY) {
    /* ok, it was locked */
    return;
  } else if (r == 0) {
    caml_fatal_error("Required mutex not locked");
  } else {
    check_err("assert_locked", r);
  }
#endif
}

void caml_plat_assert_all_locks_unlocked(void)
{
#ifdef DEBUG
  if (lockdepth) caml_fatal_error("Locks still locked at termination");
#endif
}

void caml_plat_mutex_free(caml_plat_mutex* m)
{
  check_err("mutex_free", pthread_mutex_destroy(m));
}

static void caml_plat_cond_init_aux(caml_plat_cond *cond)
{
  pthread_condattr_t attr;
  pthread_condattr_init(&attr);
#if defined(_POSIX_TIMERS) && \
    defined(_POSIX_MONOTONIC_CLOCK) && \
    _POSIX_MONOTONIC_CLOCK != (-1)
  pthread_condattr_setclock(&attr, CLOCK_MONOTONIC);
#endif
  pthread_cond_init(&cond->cond, &attr);
}

/* Condition variables */
void caml_plat_cond_init(caml_plat_cond* cond, caml_plat_mutex* m)
{
  caml_plat_cond_init_aux(cond);
  cond->mutex = m;
}

void caml_plat_wait(caml_plat_cond* cond)
{
  caml_plat_assert_locked(cond->mutex);
  check_err("wait", pthread_cond_wait(&cond->cond, cond->mutex));
}

void caml_plat_broadcast(caml_plat_cond* cond)
{
  caml_plat_assert_locked(cond->mutex);
  check_err("cond_broadcast", pthread_cond_broadcast(&cond->cond));
}

void caml_plat_signal(caml_plat_cond* cond)
{
  caml_plat_assert_locked(cond->mutex);
  check_err("cond_signal", pthread_cond_signal(&cond->cond));
}

void caml_plat_cond_free(caml_plat_cond* cond)
{
  check_err("cond_free", pthread_cond_destroy(&cond->cond));
  cond->mutex=0;
}

/* Barriers */

#ifndef CAML_PLAT_FUTEX_FALLBACK
#  if defined(_WIN32)
#    include <synchapi.h>
#    define CAML_PLAT_FUTEX_WAIT(ftx, undesired)                \
  WaitOnAddress(ftx, &undesired, sizeof(undesired), INFINITE)
#    define CAML_PLAT_FUTEX_WAKE(ftx) \
  WakeByAddressAll(ftx)

#  elif defined(__linux__)
#    include <linux/futex.h>
#    include <sys/syscall.h>
#    define CAML_PLAT_FUTEX_WAIT(ftx, undesired)    \
  syscall(SYS_futex, ftx, FUTEX_WAIT_PRIVATE,       \
          /* expected */ undesired,                 \
          /* timeout */ NULL,                       \
          /* ignored */ NULL, 0)
#    define CAML_PLAT_FUTEX_WAKE(ftx)           \
  syscall(SYS_futex, ftx, FUTEX_WAKE_PRIVATE,   \
          /* count */ INT_MAX,                  \
          /* timeout */ NULL,                   \
          /* ignored */ NULL, 0)

/* #  elif defined(__APPLE__)
   macOS has __ulock_wait which is used in implementations of libc++,
   (e.g. by LLVM) but the API is private and unstable. */

#  elif defined(__FreeBSD__)
#    include <sys/umtx.h>
#    include <sys/syscall.h>
#    define CAML_PLAT_FUTEX_WAIT(ftx, undesired)        \
  syscall(SYS__umtx_op, ftx, UMTX_OP_WAIT_UINT_PRIVATE, \
          /* expected */ undesired,                     \
          /* timeout */ NULL, NULL)
#    define CAML_PLAT_FUTEX_WAKE(ftx)              \
  syscall(SYS__umtx_op, ftx, UMTX_OP_WAKE_PRIVATE, \
          /* count */ INT_MAX,                     \
          /* unused */ NULL, NULL)

#  elif defined(__OpenBSD__)
#    include <sys/futex.h>
#    define CAML_PLAT_FUTEX_WAIT(ftx, undesired)      \
  futex((volatile uint32_t*)ftx, FUTEX_WAIT_PRIVATE,  \
        /* expected */ undesired,                     \
        /* timeout */ NULL,                           \
        /* ignored */ NULL)
#    define CAML_PLAT_FUTEX_WAKE(ftx)                \
  futex((volatile uint32_t*)ftx, FUTEX_WAKE_PRIVATE, \
        /* count */ INT_MAX,                         \
        /* ignored */ NULL, NULL)

#  elif defined(__NetBSD__)
#    include <sys/futex.h>
#    include <sys/syscall.h>
#    define CAML_PLAT_FUTEX_WAIT(ftx, undesired)    \
  syscall(SYS___futex, ftx,                         \
          FUTEX_WAIT | FUTEX_PRIVATE_FLAG,          \
          /* expected */ undesired,                 \
          /* timeout */ NULL,                       \
          /* ignored */ NULL, 0, 0)
#    define CAML_PLAT_FUTEX_WAKE(ftx)            \
  sycall(SYS___futex, ftx,                       \
         FUTEX_WAKE | FUTEX_PRIVATE_FLAG,        \
         /* count */ INT_MAX,                    \
         /* ignored */ NULL, NULL, 0, 0)

#  elif defined(__DragonFly__)
#    include <sys/syscall.h>
#    define CAML_PLAT_FUTEX_WAIT(ftx, undesired)    \
  syscall(SYS_umtx_sleep, ftx, undesired, 0)
#    define CAML_PLAT_FUTEX_WAKE(ftx)           \
  syscall(SYS_umtx_wakeup, ftx, INT_MAX)

#  else
#    error "No futex implementation available"
#  endif
#endif

#if !defined(CAML_PLAT_FUTEX_FALLBACK)

void caml_plat_futex_wait(caml_plat_futex* ftx, caml_plat_futex_value undesired) {
  while (atomic_load_acquire(&ftx->value) == undesired) {
    CAML_PLAT_FUTEX_WAIT(&ftx->value, undesired);
  }
}

void caml_plat_futex_wake_all(caml_plat_futex* ftx) {
  CAML_PLAT_FUTEX_WAKE(&ftx->value);
}

#else

void caml_plat_futex_wait(caml_plat_futex* futex, caml_plat_futex_value undesired) {
  caml_plat_lock(&futex->mutex);
  while (atomic_load_acquire(&futex->value) == undesired) {
    check_err("wait", pthread_cond_wait(&futex->cond, &futex->mutex));
  }
  caml_plat_unlock(&futex->mutex);
}

void caml_plat_futex_wake_all(caml_plat_futex* futex) {
  caml_plat_lock(&futex->mutex);
  check_err("cond_broadcast", pthread_cond_broadcast(&futex->cond));
  caml_plat_unlock(&futex->mutex);
}

void caml_plat_futex_init(caml_plat_futex* ftx, caml_plat_futex_value value) {
  ftx->value = value;
  caml_plat_mutex_init(&ftx->mutex);
  check_err("cond_init", pthread_cond_init(&ftx->cond, NULL));
}

void caml_plat_futex_free(caml_plat_futex* ftx) {
  caml_plat_mutex_free(&ftx->mutex);
  check_err("cond_destroy", pthread_cond_destroy(&ftx->cond));
}
#endif

barrier_status caml_plat_barrier_arrive(caml_plat_barrier* barrier) {
  uintnat prev_parties = atomic_fetch_add(&barrier->arrived, 1);
  return prev_parties + 1;
}

/* single-sense */

void caml_plat_barrier_release(caml_plat_barrier* barrier) {
  /* if nobody is blocking, release in user-space */
  if (atomic_exchange(&barrier->futex.value, Barrier_released) != Barrier_uncontested) {
    /* at least one thread is (going to be) blocked on the futex, notify */
    caml_plat_futex_wake_all(&barrier->futex);
  }
}

static void caml_plat_barrier_wait(caml_plat_barrier* barrier) {
  /* indicate that we are about to block */
  caml_plat_futex_value expected = Barrier_uncontested;
  (void)atomic_compare_exchange_strong(&barrier->futex.value, &expected, Barrier_contested);
  /* it's either already released (== Barrier_released), or we are
     going to block (== Barrier_contested), futex_wait() here will
     take care of both */
  caml_plat_futex_wait(&barrier->futex, Barrier_contested);
}

/* sense-reversing */
/* futex states:
   - X...0 if nobody is blocking (but they may be spinning)
   - X...1 if anybody is blocking (or about to)

   where X is the sense bit
 */

void caml_plat_barrier_flip(caml_plat_barrier* barrier, barrier_status current_sense) {
  uintnat new_sense = current_sense ^ BARRIER_SENSE_BIT;
  atomic_store_relaxed(&barrier->arrived, new_sense);
  /* if a thread observes the flip below, it will also observe the
     reset counter, since any currently waiting threads will check the
     futex before leaving, they will see the counter correctly */

  caml_plat_futex_value
    current_sense_word = (caml_plat_futex_value) current_sense,
    new_sense_word = (caml_plat_futex_value) new_sense;

  /* if nobody is blocking, flip in user-space */
  if (atomic_exchange(&barrier->futex.value, new_sense_word) != current_sense_word) {
    /* a thread is (about to be) blocked, notify */
    caml_plat_futex_wake_all(&barrier->futex);
  }
}

static void caml_plat_barrier_wait_sense(caml_plat_barrier* barrier, unsigned current_sense) {
  /* indicate that we are about to block */
  caml_plat_futex_value sense_bit = current_sense ? BARRIER_SENSE_BIT : 0;
  caml_plat_futex_value expected = sense_bit;
  (void)atomic_compare_exchange_strong(&barrier->futex.value, &expected, sense_bit | 1);
  /* wait until the sense changes */
  caml_plat_futex_wait(&barrier->futex, sense_bit | 1);
}

/* Memory management */

static uintnat round_up(uintnat size, uintnat align) {
  CAMLassert(Is_power_of_2(align));
  return (size + align - 1) & ~(align - 1);
}

intnat caml_plat_pagesize = 0;
intnat caml_plat_mmap_alignment = 0;

uintnat caml_mem_round_up_pages(uintnat size)
{
  return round_up(size, caml_plat_pagesize);
}

#define Is_page_aligned(size) ((size & (caml_plat_pagesize - 1)) == 0)

#ifdef DEBUG
static struct lf_skiplist mmap_blocks = {NULL};
#endif

#ifndef _WIN32
#endif

void* caml_mem_map(uintnat size, uintnat alignment, int reserve_only)
{
  CAMLassert(Is_power_of_2(alignment));
  CAMLassert(Is_page_aligned(size));
  alignment = round_up(alignment, caml_plat_mmap_alignment);

#ifdef DEBUG
  if (mmap_blocks.head == NULL) {
    /* The first call to caml_mem_map should be during caml_init_domains, called
       by caml_init_gc during startup - i.e. before any domains have started. */
    CAMLassert(atomic_load_acquire(&caml_num_domains_running) <= 1);
    caml_lf_skiplist_init(&mmap_blocks);
  }
#endif

  void* mem = caml_plat_mem_map(size, alignment, reserve_only);

  if (mem == 0) {
    caml_gc_message(0x1000, "mmap %" ARCH_INTNAT_PRINTF_FORMAT "d bytes failed",
                            size);
    return 0;
  }

  caml_gc_message(0x1000, "mmap %" ARCH_INTNAT_PRINTF_FORMAT "d"
                          " bytes at %p for heaps\n", size, mem);

#ifdef DEBUG
  caml_lf_skiplist_insert(&mmap_blocks, (uintnat)mem, size);
#endif

  return mem;
}

void* caml_mem_commit(void* mem, uintnat size)
{
  CAMLassert(Is_page_aligned(size));
  caml_gc_message(0x1000, "commit %" ARCH_INTNAT_PRINTF_FORMAT "d"
                          " bytes at %p for heaps\n", size, mem);
  return caml_plat_mem_commit(mem, size);
}

void caml_mem_decommit(void* mem, uintnat size)
{
  if (size) {
    caml_gc_message(0x1000, "decommit %" ARCH_INTNAT_PRINTF_FORMAT "d"
                            " bytes at %p for heaps\n", size, mem);
    caml_plat_mem_decommit(mem, size);
  }
}

void caml_mem_unmap(void* mem, uintnat size)
{
#ifdef DEBUG
  uintnat data;
  CAMLassert(caml_lf_skiplist_find(&mmap_blocks, (uintnat)mem, &data) != 0);
  CAMLassert(data == size);
#endif
  caml_gc_message(0x1000, "munmap %" ARCH_INTNAT_PRINTF_FORMAT "d"
                          " bytes at %p for heaps\n", size, mem);
  caml_plat_mem_unmap(mem, size);
#ifdef DEBUG
  caml_lf_skiplist_remove(&mmap_blocks, (uintnat)mem);
#endif
}

#define Min_sleep_ns       10000 // 10 us
#define Slow_sleep_ns    1000000 //  1 ms
#define Max_sleep_ns  1000000000 //  1 s

Caml_inline unsigned get_next_spins(unsigned *spins) {
  if (*spins < Min_sleep_ns) *spins = Min_sleep_ns;
  if (*spins > Max_sleep_ns) *spins = Max_sleep_ns;
  return *spins + *spins / 4;
}

unsigned caml_plat_spin_yield(unsigned spins) {
  unsigned next_spins = get_next_spins(&spins);
  usleep(spins/1000);
  return next_spins;
}

unsigned caml_plat_spin_block(unsigned spins,
                              enum caml_plat_wait_type wait_type,
                              void* obj,
                              caml_plat_futex_value value,
                              const struct caml_plat_srcloc* loc)
{
  switch (wait_type) {
  case CamlWaitBarrier:
    caml_plat_barrier_wait(obj);
    break;
  case CamlWaitBarrierSense:
    caml_plat_barrier_wait_sense(obj, !!value);
    break;
  case CamlWaitFutex:
    caml_plat_futex_wait(obj, value);
    break;
  default: {
    unsigned next_spins = get_next_spins(&spins);
    if (spins < Slow_sleep_ns && Slow_sleep_ns <= next_spins) {
      caml_gc_log("Slow spin-wait loop in %s at %s:%d",
                  loc->function, loc->file, loc->line);
    }
    usleep(spins/1000);
    return next_spins;
  }
  }
  return spins;
}
