//
//  gc.h
//  CLOJURE_METAL
//
//  Created by Timothy Baldridge on 1/4/14.
//
//

#ifndef CLOJURE_METAL_gc_h
#define CLOJURE_METAL_gc_h
#include "stddef.h"


#ifdef __cplusplus
extern "C" {
#endif

    typedef size_t (*cm_obj_scan)(void* ss, void* base, void* limit);
    typedef void (*cm_obj_fwd)(void* old_loc, void* new_loc);
    typedef void (*cm_obj_pad)(void* old_loc, size_t size);
    typedef void* (*cm_obj_skip)(void* base);
    typedef void* (*cm_obj_isfwd)(void* addr);
    
    
void cm_init_gc(size_t alignment,
                cm_obj_scan scan,
                cm_obj_fwd fwd,
                cm_obj_pad pad,
                cm_obj_skip skip,
                cm_obj_isfwd isfwd);

void* cm_gc_mark_stack(void** marker);

int cm_pool_amc_reserve(void **loc, size_t size);
int cm_pool_amc_commit(void **loc, size_t size);
void cm_gc_register_root(void** addr);
    
#ifdef __cplusplus
}
#endif

#endif
