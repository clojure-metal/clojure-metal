#include "gtest/gtest.h"
#include "cmsl/gc.h"

enum Types {
    FWD,
    FWD_SMALL,
    PAD,
    CONS,
    INT
};


typedef struct fwd_small_t
{
    size_t tid;
    void* newloc;
} fwd_small_t;

typedef struct fwd_t
{
    size_t tid;
    void* newloc;
    size_t size;
} fwd_t;

typedef struct pad_t
{
    size_t tid;
    size_t size;
} pad_t;

typedef struct cons_t
{
    size_t tid;
    void* first;
    void* next;
} cons_t;

typedef struct int_t
{
    size_t tid;
    size_t val; // signed in the actual use case, but still word sized
} int_t;

#define ALIGNMENT (sizeof(pad_t))

/* Align size upwards to the next multiple of the word size. */
#define ALIGN_WORD(size) \
(((size) + ALIGNMENT - 1) & ~(ALIGNMENT - 1))


size_t sizes[] =
{ ALIGN_WORD(sizeof(fwd_t)),
  ALIGN_WORD(sizeof(fwd_small_t)),
    ALIGN_WORD(sizeof(pad_t)),
    ALIGN_WORD(sizeof(cons_t)),
    ALIGN_WORD(sizeof(int_t))
    
};

#define TYPEID(x) *((size_t *)x)



// This object is called to skip over a object. The GC often allocates blocks
// of memory and then paritions them up for individual objects. The empty space
// must be filled with something that the GC can recognize.

void *obj_skip(void* base)
{
    size_t tid = TYPEID(base);
    if (tid == FWD)
    {
        return (char *)base + ((fwd_t *)base)->size;
    }
    else if (tid == PAD)
    {
        return (char *)base + ((pad_t *)base)->size;
    }
    return (char *)base + sizes[tid];
}

//extracted from mps header files
typedef struct ss_t {
    size_t _zs, _w, _ufs;
} ss_t;

#define MPS_FIX1(ss, ref) \
(_mps_wt = (size_t)1 << ((size_t)(ref) >> _mps_zs \
& (sizeof(size_t) * CHAR_BIT - 1)), \
_mps_ufs |= _mps_wt, \
(_mps_w & _mps_wt) != 0)

extern "C" {
extern size_t _mps_fix2(void *, void *);
}
#define MPS_FIX2(ss, ref_io) _mps_fix2(ss, ref_io)

#define MPS_FIX12(ss, ref_io) \
(MPS_FIX1(ss, *(ref_io)) ? \
MPS_FIX2(ss, ref_io) : 0)

#define FIX(ref)                                                        \
do {                                                                \
void* _addr = ref; /* copy to local to avoid type pun */ \
size_t res = MPS_FIX12(ss, &_addr);                          \
if (res != 0) return res;                              \
(ref) = _addr;                                                  \
} while (0)

#define CM_BEGIN_ALLOC_AMC(klass, nm) \
klass *nm; \
do { \
size_t size = ALIGN_WORD(sizeof(klass)); \
do { \
cm_pool_amc_reserve((void **)&nm, size); \

#define CM_END_ALLOC_AMC(nm) \
} while(!cm_pool_amc_commit((void **)&nm, size)); \
} while(false);



size_t obj_scan(void *ss, void* base, void* limit)
{
    ss_t *_ss = (ss_t *)ss;
    size_t _mps_zs = (_ss)->_zs;
    size_t _mps_w = (_ss)->_w;
    size_t _mps_ufs = (_ss)->_ufs;
    size_t _mps_wt;
    while (base < limit)
    {
        // only need to scan fwd_t, fwd_small_t, and cons_t
        size_t tid = TYPEID(base);
        if (tid == FWD)
        {
            
        }
        if (tid == FWD_SMALL)
        {
            
        }
        if (tid == CONS)
        {
            cons_t *obj = (cons_t *)base;
            FIX(obj->first);
            FIX(obj->next);
        }
        base = obj_skip(base);
        
    }
    (_ss)->_ufs = _mps_ufs;
    return 0;
}

void obj_pad(void *old, size_t size)
{
    if (size >= sizeof(cm_obj_pad))
    {
        auto obj = (pad_t *)old;
        obj->tid = PAD;
        obj->size = size;
        return;
    }
    exit(-1); // Shouldn't happen since sizeof(pad_t) == ALIGNMENT
}

// If this object is a fwd object, return a pointer to the new
// location of the object. Otherwise return nullptr.
void *obj_isfwd(void *base)
{
    if (TYPEID(base) == FWD || TYPEID(base) == FWD_SMALL)
        // we can do this, since new_loc is in the same palce in both structs
        return ((fwd_small_t *)base)->newloc;
    return nullptr;
}


// When the GC moves an object, it calls this function. It is our job
// to update the old location with a pointer to where the new object lives.
// Since the fwd_t object may be larger than the space of the old object,
// we have to define two objects. We use the smaller object when we know the
// exact size of the old object is 2 words (or ALIGNMENT).
void obj_fwd(void* old_loc, void* new_loc)
{
    size_t size = sizes[TYPEID(old_loc)];
    if (size == sizeof(fwd_small_t))
    {
        auto obj = (fwd_small_t *)old_loc;
        obj->tid = FWD_SMALL;
        obj->newloc = new_loc;
    }
    else {
        auto obj = (fwd_t *)old_loc;
        obj->tid = FWD;
        obj->newloc = new_loc;
        obj->size = size;
    }
}

void *wrap_int(size_t i)
{
    CM_BEGIN_ALLOC_AMC(int_t, c)
    c->tid = INT;
    c->val = i;
    CM_END_ALLOC_AMC(c)
    
    return c;
}

void *cons(void *head, void* tail)
{
    CM_BEGIN_ALLOC_AMC(cons_t, c)
    c->tid = CONS;
    c->first = head;
    c->next = tail;
    CM_END_ALLOC_AMC(c)
    
    return c;
}

TEST(gc_tests, alloc_cons)
{
    // This test just exercises the GC to flush out any
    // collection issues. On my machine (64bit OSX) this code
    // sits around 500KB of memory.
    void *c = nullptr;
    for (int x = 0; x < 1024 * 1024 * 10; x ++)
    {
        c = cons(wrap_int(x), wrap_int(x + 1));
    }
}


int main(int argc, char* argv[])
{
   
    cm_init_gc(ALIGNMENT,
               &obj_scan,
               &obj_fwd,
               &obj_pad,
               &obj_skip,
               &obj_isfwd);
    void* marker;
    cm_gc_mark_stack(&marker);
    
   
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

