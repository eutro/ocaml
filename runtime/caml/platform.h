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

#ifndef CAML_PLAT_THREADS_H
#define CAML_PLAT_THREADS_H
/* Platform-specific concurrency and memory primitives */

#ifdef CAML_INTERNALS

#include <pthread.h>
#include <errno.h>
#include <string.h>
#include "config.h"
#include "mlvalues.h"
#include "sys.h"

#if defined(MAP_ANON) && !defined(MAP_ANONYMOUS)
#define MAP_ANONYMOUS MAP_ANON
#endif

/* Hint for busy-waiting loops */

Caml_inline void cpu_relax(void) {
#ifdef __GNUC__
#if defined(__x86_64__) || defined(__i386__)
  __asm__ volatile("pause" ::: "memory");
#elif defined(__aarch64__)
  __asm__ volatile ("yield" ::: "memory");
#elif defined(__riscv)
  /* Encoding of the pause instruction */
  __asm__ volatile (".4byte 0x100000F");
#elif defined(__ppc64__)
  __asm__ volatile ("or 1, 1, 1 # low priority");
  __asm__ volatile ("or 2, 2, 2 # medium priority");
  __asm__ volatile ("" ::: "memory");
#else
  /* Just a compiler barrier */
  __asm__ volatile ("" ::: "memory");
#endif
#endif
}

/* Loads and stores with acquire, release and relaxed semantics */

#define atomic_load_acquire(p)                    \
  atomic_load_explicit((p), memory_order_acquire)
#define atomic_load_relaxed(p)                    \
  atomic_load_explicit((p), memory_order_relaxed)
#define atomic_store_release(p, v)                      \
  atomic_store_explicit((p), (v), memory_order_release)
#define atomic_store_relaxed(p, v)                      \
  atomic_store_explicit((p), (v), memory_order_relaxed)

/* Atomic read-modify-write instructions, with full fences */

Caml_inline uintnat atomic_fetch_add_verify_ge0(atomic_uintnat* p, uintnat v) {
  uintnat result = atomic_fetch_add(p,v);
  CAMLassert ((intnat)result > 0);
  return result;
}


typedef pthread_mutex_t caml_plat_mutex;
#define CAML_PLAT_MUTEX_INITIALIZER PTHREAD_MUTEX_INITIALIZER
void caml_plat_mutex_init(caml_plat_mutex*);
Caml_inline void caml_plat_lock(caml_plat_mutex*);
Caml_inline int caml_plat_try_lock(caml_plat_mutex*);
void caml_plat_assert_locked(caml_plat_mutex*);
void caml_plat_assert_all_locks_unlocked(void);
Caml_inline void caml_plat_unlock(caml_plat_mutex*);
void caml_plat_mutex_free(caml_plat_mutex*);
typedef struct { pthread_cond_t cond; caml_plat_mutex* mutex; } caml_plat_cond;
#define CAML_PLAT_COND_INITIALIZER(m) { PTHREAD_COND_INITIALIZER, m }
void caml_plat_cond_init(caml_plat_cond*, caml_plat_mutex*);
void caml_plat_wait(caml_plat_cond*);
/* like caml_plat_wait, but if nanoseconds surpasses the second parameter
   without a signal, then this function returns 1. */
void caml_plat_broadcast(caml_plat_cond*);
void caml_plat_signal(caml_plat_cond*);
void caml_plat_cond_free(caml_plat_cond*);

/* Barriers */

typedef struct caml_plat_futex caml_plat_futex;

typedef uint32_t caml_plat_futex_value;
typedef _Atomic caml_plat_futex_value caml_plat_futex_word;

/* Define CAML_PLAT_FUTEX_FALLBACK to use the condition-variable
   fallback, even if a futex implementation is available */
#ifndef CAML_PLAT_FUTEX_FALLBACK
#  if defined(_WIN32)                                   \
  || (defined(__linux__) && defined(HAS_LINUX_FUTEX_H)) \
  || defined(__FreeBSD__) || defined(__OpenBSD__)
/*  These exist, but are untested
      defined(__NetBSD__) || defined(__DragonFly__) */
#  else
#    define CAML_PLAT_FUTEX_FALLBACK
#  endif
#endif

#if !defined(CAML_PLAT_FUTEX_FALLBACK)
struct caml_plat_futex {
  caml_plat_futex_word value;
};
#  define CAML_PLAT_FUTEX_INITIALIZER(value) { (value) }

Caml_inline void caml_plat_futex_init(caml_plat_futex* ftx, caml_plat_futex_value value) {
  ftx->value = value;
}
Caml_inline void caml_plat_futex_free(caml_plat_futex* ftx) {
  (void) ftx; /* noop */
}
#else
struct caml_plat_futex {
  caml_plat_futex_word value;
  caml_plat_mutex mutex;
  pthread_cond_t cond;
};
#  define CAML_PLAT_FUTEX_INITIALIZER(value) \
  { value, CAML_PLAT_MUTEX_INITIALIZER, PTHREAD_COND_INITIALIZER }

void caml_plat_futex_init(caml_plat_futex* ftx, caml_plat_futex_value value);
void caml_plat_futex_free(caml_plat_futex*);
#endif

void caml_plat_futex_wait(caml_plat_futex* futex, caml_plat_futex_value undesired);
void caml_plat_futex_wake_all(caml_plat_futex* futex);

/*
 * A barrier that can be either single-sense or sense-reversing.
 *
 * Single-sense:
 * - The barrier must be `caml_plat_barrier_reset` to block new arrivals.
 * - When a thread arrives, it should call `caml_plat_barrier_arrive` to retrieve
 *   the number of parties.
 * - If a thread is the last to arrive, it should call `caml_plat_barrier_release`
 *   to release other threads.
 * - If a thread isn't the last, it should wait for the barrier to be released,
 *   using SPIN_WAIT_ON(BARRIER(b)), and checking `caml_plat_barrier_is_released`.
 * - If released, any new arrivals will pass through, until `caml_plat_barrier_reset`
 *   is called again.
 *
 * Sense-reversing:
 * - The barrier does not need to be explicitly reset.
 * - When a thread arrives, it should call `caml_plat_barrier_arrive` to atomically
 *   increment the number of parties and retrieve the current sense.
 * - If a thread is the last to arrive, it should call `caml_plat_barrier_flip`,
 *   releasing waiting threads and resetting barrier.
 * - If a thread is not the last to arrive, it should wait for the sense to be flipped
 *   using SPIN_WAIT_ON(BARRIER_SENSE(b, sense)).
 */
typedef struct caml_plat_barrier {
  caml_plat_futex futex;
  atomic_uintnat arrived; /* includes sense bit */
} caml_plat_barrier;
#define CAML_PLAT_BARRIER_INITIALIZER \
  { CAML_PLAT_FUTEX_INITIALIZER(0), ATOMIC_UINTNAT_INIT(0) }

typedef uintnat barrier_status;
/* Arrive at the barrier, returns the number of parties that have
   arrived at the barrier (including this one); the caller should
   check whether it is the last expected party to arrive, and release
   or flip the barrier if so.

   In a sense-reversing barrier, this also encodes the current sense
   of the barrier in BARRIER_SENSE_BIT, which should be masked off if
   checking for the last arrival. */
barrier_status caml_plat_barrier_arrive(caml_plat_barrier*);
#define BARRIER_SENSE_BIT 0x100000

/* -- Single-sense --

   Futex states:
   - 0 if released
   - 1 if nobody is blocking (but they may be spinning)
   - 2 if anybody is blocking (or about to)
 */
#define Barrier_released 0
#define Barrier_uncontested 1
#define Barrier_contested 2
/* Reset the barrier to 0 arrivals, block new waiters */
Caml_inline void caml_plat_barrier_reset(caml_plat_barrier* barrier) {
  atomic_store_relaxed(&barrier->futex.value, Barrier_uncontested);
  /* threads check arrivals before the futex, 'release' ordering
     ensures they see it reset */
  atomic_store_release(&barrier->arrived, 0);
}
/* Release the barrier unconditionally, letting all parties through */
void caml_plat_barrier_release(caml_plat_barrier*);
/* Check if the barrier has been released */
Caml_inline int caml_plat_barrier_is_released(caml_plat_barrier* barrier) {
  return atomic_load_acquire(&barrier->futex.value) == Barrier_released;
}

/* -- Sense-reversing -- */
/* Flip the sense of the barrier, releasing current waiters and
   blocking new ones.

   `current_sense` should be just `(b & BARRIER_SENSE_BIT)`
   with b as returned by `caml_plat_barrier_arrive`. */
void caml_plat_barrier_flip(caml_plat_barrier*, barrier_status current_sense);
Caml_inline int caml_plat_barrier_sense_has_flipped(
  caml_plat_barrier* barrier,
  barrier_status current_sense
) {
  return (atomic_load_acquire(&barrier->futex.value) & BARRIER_SENSE_BIT) != current_sense;
}

/* Spin-wait loops */

#define GENSYM_3(name, l) name##l
#define GENSYM_2(name, l) GENSYM_3(name, l)
#define GENSYM(name) GENSYM_2(name, __LINE__)

/*
  The SPIN_WAIT* macros below all expand to the header of a `for` loop
  (with some (GENSYM'd) local variable declarations before) that
  implement spin wait loops, running hot several times before starting
  to yield to the OS.

  Spin wait loops can optionally block on OS-based synchronisation
  (barriers/futexes) after a while, by passing BARRIER(b),
  BARRIER_SENSE(b, sense) or FUTEX(f, undesired) to
  SPIN_WAIT_ON.
 */

#define Max_spins 1000
#define Max_spins_contested(ndomains) ((ndomains) > 2 ? 100 : Max_spins)
#define Max_spins_to_block 100000 // 100 us

#define SPIN_WAIT_ON_FOR(waited, max_spins, spins_to_block) \
  unsigned GENSYM(caml__max_spins) = max_spins;             \
  unsigned GENSYM(caml__spins_to_block) = spins_to_block;   \
  SPIN_WAIT_ON_##waited
#define SPIN_WAIT_ON(waited) SPIN_WAIT_ON_FOR(waited, Max_spins, Max_spins_to_block)
#define SPIN_WAIT SPIN_WAIT_ON(NOTHING)

#define SPIN_WAIT_ON_NOTHING \
  SPIN_WAIT_IMPL(Nothing, 0, 0)
#define SPIN_WAIT_ON_BARRIER(barrier) \
  SPIN_WAIT_IMPL(Barrier, barrier, 0)
#define SPIN_WAIT_ON_BARRIER_SENSE(barrier, sense) \
  SPIN_WAIT_IMPL(BarrierSense, barrier, !!sense)
#define SPIN_WAIT_ON_FUTEX(futex, value) \
  SPIN_WAIT_IMPL(Futex, futex, value)

enum caml_plat_wait_type {
  CamlWaitNothing,
  CamlWaitBarrier,
  CamlWaitBarrierSense,
  CamlWaitFutex,
};

struct caml_plat_srcloc {
  const char* file;
  int line;
  const char* function;
};

CAMLextern unsigned caml_plat_spin_yield(unsigned spins);
CAMLextern unsigned caml_plat_spin_block(unsigned spins,
                                         enum caml_plat_wait_type wait_type,
                                         void* obj,
                                         caml_plat_futex_value value,
                                         const struct caml_plat_srcloc* loc);

Caml_inline unsigned caml_plat_spin_step(unsigned spins,
                                         unsigned max_spins,
                                         unsigned spins_to_block,
                                         enum caml_plat_wait_type wait_type,
                                         void* obj,
                                         caml_plat_futex_value value,
                                         const struct caml_plat_srcloc *loc) {
  cpu_relax();
  if (CAMLlikely(spins < max_spins)) {
    return spins + 1;
  } else if (CAMLlikely(spins < spins_to_block)) {
    return caml_plat_spin_yield(spins);
  } else {
    return caml_plat_spin_block(spins, wait_type, obj, value, loc);
  }
}

#define SPIN_WAIT_IMPL(Type, obj, value)                                \
  unsigned GENSYM(caml__spins) = 0;                                     \
  static const struct caml_plat_srcloc GENSYM(caml__loc) = {            \
    __FILE__, __LINE__, __func__                                        \
  };                                                                    \
  for (; 1; GENSYM(caml__spins) = caml_plat_spin_step(                  \
         GENSYM(caml__spins), GENSYM(caml__max_spins),                  \
         GENSYM(caml__spins_to_block),                                  \
         CamlWait##Type, obj, value,                                    \
         &GENSYM(caml__loc)))

/* Memory management primitives (mmap) */

uintnat caml_mem_round_up_pages(uintnat size);
/* The size given to caml_mem_map and caml_mem_commit must be a multiple of
   caml_plat_pagesize. The size given to caml_mem_unmap and caml_mem_decommit
   must match the size given to caml_mem_map/caml_mem_commit for mem.

   The Windows and Cygwin implementations do not support arbitrary alignment
   and will fail for alignment values greater than caml_plat_mmap_alignment.
   Luckily, this value is rather large on those platforms: 64KiB. This is enough
   for all alignments used in the runtime system so far, the larger being the
   major heap pools aligned on 32KiB boundaries. */
void* caml_mem_map(uintnat size, uintnat alignment, int reserve_only);
void* caml_mem_commit(void* mem, uintnat size);
void caml_mem_decommit(void* mem, uintnat size);
void caml_mem_unmap(void* mem, uintnat size);


CAMLnoret void caml_plat_fatal_error(const char * action, int err);

Caml_inline void check_err(const char* action, int err)
{
  if (err) caml_plat_fatal_error(action, err);
}

#ifdef DEBUG
static __thread int lockdepth;
#define DEBUG_LOCK(m) (lockdepth++)
#define DEBUG_UNLOCK(m) (lockdepth--)
#else
#define DEBUG_LOCK(m)
#define DEBUG_UNLOCK(m)
#endif

Caml_inline void caml_plat_lock(caml_plat_mutex* m)
{
  check_err("lock", pthread_mutex_lock(m));
  DEBUG_LOCK(m);
}

Caml_inline int caml_plat_try_lock(caml_plat_mutex* m)
{
  int r = pthread_mutex_trylock(m);
  if (r == EBUSY) {
    return 0;
  } else {
    check_err("try_lock", r);
    DEBUG_LOCK(m);
    return 1;
  }
}

Caml_inline void caml_plat_unlock(caml_plat_mutex* m)
{
  DEBUG_UNLOCK(m);
  check_err("unlock", pthread_mutex_unlock(m));
}

extern intnat caml_plat_pagesize;
extern intnat caml_plat_mmap_alignment;

#endif /* CAML_INTERNALS */

#endif /* CAML_PLATFORM_H */
