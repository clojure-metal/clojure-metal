//
//  gc.c
//  CLOJURE_METAL
//
//  Created by Timothy Baldridge on 1/4/14.
//
//

#include "gc.h"
#include <atomic>
#include "stdio.h"
#include "stdlib.h"

#define ERROR(s) {printf("%s\n", s); exit(1);}

extern "C" {
#include "mps.h"
#include "mpsavm.h"
#include "mpscams.h"
#include "mpscamc.h"
#include "mpstd.h"
};

typedef struct pool_amc_data_t
{
    mps_fmt_t obj_fmt;
    mps_chain_t obj_chain;
    mps_root_t globals_root;
    
    mps_arena_t arena;
    mps_pool_t obj_pool;
    mps_ap_t obj_ap;
} pool_amc_data_t;

void* pool_amc_ap;

mps_gen_param_s obj_gen_params[] = {
    { 150, 0.85},
    { 170, 0.45},
};


pool_amc_data_t pool_amc_data;

void cm_init_gc(size_t alignment,
                   cm_obj_scan scan,
                   cm_obj_fwd fwd,
                   cm_obj_pad pad,
                   cm_obj_skip skip,
                   cm_obj_isfwd isfwd)
{
    mps_res_t res;
    MPS_ARGS_BEGIN(args) {
        MPS_ARGS_ADD(args, MPS_KEY_ARENA_SIZE, 32 * 1024 * 1024);
        MPS_ARGS_DONE(args);
        res = mps_arena_create_k(&pool_amc_data.arena, mps_arena_class_vm(), args);
    } MPS_ARGS_END(args);
    if (res != MPS_RES_OK) ERROR("Couldn't create area");
    
    MPS_ARGS_BEGIN(args) {
        MPS_ARGS_ADD(args, MPS_KEY_FMT_ALIGN, alignment);
        MPS_ARGS_ADD(args, MPS_KEY_FMT_SCAN, (mps_fmt_scan_t)scan);
        MPS_ARGS_ADD(args, MPS_KEY_FMT_SKIP, (mps_fmt_skip_t)skip);
        MPS_ARGS_ADD(args, MPS_KEY_FMT_FWD, (mps_fmt_fwd_t)fwd);
        MPS_ARGS_ADD(args, MPS_KEY_FMT_ISFWD, (mps_fmt_isfwd_t)isfwd);
        MPS_ARGS_ADD(args, MPS_KEY_FMT_PAD, (mps_fmt_pad_t)pad);
        MPS_ARGS_DONE(args);
        res = mps_fmt_create_k(&pool_amc_data.obj_fmt, pool_amc_data.arena, args);
    } MPS_ARGS_END(args);
    if (res != MPS_RES_OK) ERROR("Couldn't create obj format");
    
    res = mps_chain_create(&pool_amc_data.obj_chain,
                           pool_amc_data.arena,
                           2,
                           obj_gen_params);
    if (res != MPS_RES_OK) ERROR("Couldn't create obj chain");
    
    
    MPS_ARGS_BEGIN(args) {
        MPS_ARGS_ADD(args, MPS_KEY_CHAIN, pool_amc_data.obj_chain);
        MPS_ARGS_ADD(args, MPS_KEY_FORMAT, pool_amc_data.obj_fmt);
        MPS_ARGS_DONE(args);
        res = mps_pool_create_k(&pool_amc_data.obj_pool, pool_amc_data.arena, mps_class_amc(), args);
    } MPS_ARGS_END(args);
    if (res != MPS_RES_OK) ERROR("Couldn't create obj pool");
    
    
    //res = mps_root_create(&pool_amc_data.globals_root, pool_amc_data.arena, mps_rank_exact(), 0,
    //                      globals_scan, NULL, 0);
    //if (res != MPS_RES_OK) ERROR("Couldn't register globals root");
    
    res = mps_ap_create_k(&pool_amc_data.obj_ap, pool_amc_data.obj_pool, mps_args_none);
    if (res != MPS_RES_OK) ERROR("Couldn't create obj allocation point");
    
    //chatter = new std::thread(chatter_handler);
    //mps_message_type_enable(arena, mps_message_type_finalization());
    
    pool_amc_ap = pool_amc_data.obj_ap;

}

int cm_pool_amc_reserve(void **p, size_t size)
{
    mps_addr_t addr;
    mps_res_t res = mps_reserve(&addr, pool_amc_data.obj_ap, size);
    if (res != MPS_RES_OK) ERROR("out of memory in create");
    *p = addr;
    return res;
}

typedef struct thread_ctx_t
{
    mps_thr_t thread;
    mps_root_t reg_root;
} thread_ctx_t;

int cm_pool_amc_commit(void **p, size_t size)
{
    return mps_commit(pool_amc_data.obj_ap, p, size);
}

void* cm_gc_mark_stack(void **marker)
{
    mps_res_t res;
    thread_ctx_t *ctx = (thread_ctx_t *)malloc(sizeof(thread_ctx_t));
    res = mps_thread_reg(&ctx->thread, pool_amc_data.arena);
    if (res != MPS_RES_OK) ERROR("Unable to Register thread!");
    
    res = mps_root_create_reg(&ctx->reg_root,
                              pool_amc_data.arena,
                              mps_rank_ambig(),
                              0,
                              ctx->thread,
                              mps_stack_scan_ambig,
                              marker,
                              0);
    
    if (res != MPS_RES_OK) ERROR("Couldn't create root");
    
    return ctx;
}

