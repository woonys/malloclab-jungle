/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "jungle3rd_week6_team4_segregation",
    /* First member's full name */
    "Jaewoon Kim",
    /* First member's email address */
    "wodns1324@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define ALIGNMENT 8 // 더블워드로 정렬
#define ALIGN(size) (((size)+ (ALIGNMENT-1)) & ~0x7) // 사이즈가 0보다 작으면 0으로, 0~8사이면 8, 8보다 크면 8의 배수로

//sizeof(size_t) = 8, ALIGN(sizeof(size_t)) = 8
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* basic constants and macros */

#define WSIZE 4 // 워드 사이즈: 4바이트
#define DSIZE 8 // 더블 워드 사이즈: 8바이트
#define CHUNKSIZE (1<<12)
#define LISTLIMIT 20 // 최대 2**20까지 사이즈

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // x가 y보다 크면 x/ 작으면 y

/* pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | alloc) // size비트와 alloc 비트 합집합 하면 하나의 헤더/footer에 들어가는 데이터 만들 수 있음.

/* read and write a word at address p */
#define GET(p) (*(unsigned int*)(p)) //unsigned int형 포인터 p가 가리키는 주소에 들어있는 값(val)을 가져온다.
#define PUT(p, val) (*(unsigned int*)(p) = (val)) // p가 가리키는 주소에 들어있는 값을 val로 넣는다.

/* Read the size and allocated fields from address p*/
#define GET_SIZE(p) (p & ~0x7)
#define GET_ALLOC(p) (p & 0x1) // 끝자리만 확인하면 오케이

/* Given block ptr bp, compute address of its header and footer */
// free면 bp가 PREC
#define HDRP(bp) ((char*)(bp)-WSIZE) 
#define FTRP(bp) ((char*)bp + GET_SIZE((HDRP)(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* get free list's SUCC and PREC pointer */
#define PRED_FREE(bp) (*(char **)(bp))
#define SUCC_FREE(bp) (*(char **)(bp + WSIZE))



static void *heap_listp;
static void *segregation_list[LISTLIMIT];

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void remove_block(void *bp);
static void insert_block(void *bp, size_t size);


/* mm_init: 패키지 초기화 */

int mm_init(void)
{
    int list;

    for (list = 0; list < LISTLIMIT; list++) {
        segregation_list[list] = NULL;
    }

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0); // Alignment padding
    PUT(heap_listp + (1* WSIZE), PACK(DSIZE, 1)); // Prologue header -> 더블워드 사이즈에 할당
    PUT(heap_listp + (2* WSIZE), PACK(DSIZE, 1)); // Prologue footer -> 더블워드 사이즈에 할당
    PUT(heap_listp + (3* WSIZE), PACK(0, 1)); // Epilogue footer -> 사이즈는 0 & 할당! 나중에 이게 중요.
    heap_listp = heap_listp + 2*WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

void *mm_malloc(size_t size)
{
    int asize = ALIGN(size + SIZE_T_SIZE);

    // size_t asize => adjusted block size
    size_t extendsize; // Amount to extend heap if no fit
    char *bp;

    // Search the free list for a fit
    if ((bp = find_fit(asize)) != NULL) {
        
        place(bp, asize);
        return bp;
    }

    // No fit found. Get more memory and place the block.
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/* mm_free: Freeing a block does nothing. */

void mm_free(void *ptr) {
    
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

// mm_realloc

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));

    if (size == 0){
        mm_free(ptr);
        return NULL;
    }

    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    // 처음(mm_init 에서 올 때) bp의 정확한 위치는 ??
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    //전 블록 가용한지
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    //다음 블록 가용한지
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc){
        insert_block(bp,size);
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        remove_block(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        // 왜 이게 아니지?? - PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        // 왜냐면!-- size가 이미 바껴서 FTRP(bp)하면 합쳐진 블록의 끝을 잘 찾는다!!
    }
    // 이전블록만 가가용 가능 하면
    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        remove_block(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc)
    {
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_block(bp, size);
    return bp;
}

static void *place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_block(bp);
    // 필요한 블록 이외에 남는게 16바이트 이상이면 - free header, footer 들어갈 자리 2워드 + payload 2워드?
    if ((csize - asize) >= (2 * DSIZE))
    {
        if (asize>=100){
            PUT(HDRP(bp), PACK(csize - asize, 0));
            PUT(FTRP(bp), PACK(csize - asize, 0));
            bp = NEXT_BLKP(bp);
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            coalesce(PREV_BLKP(bp));
            return bp;
        }
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
        return PREV_BLKP(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        return bp;
    }
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;

    int list = 0;
    size_t searchsize = asize;

    while (list < LISTLIMIT){
        if ((list == LISTLIMIT-1) || (searchsize <= 1)&&(segregation_list[list] != NULL)){
            bp = segregation_list[list];

            while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))){
                bp = SUCC_FREE(bp);
            }
            if (bp != NULL){
                return bp;
            }
        }
        searchsize >>= 1;
        list++;
    }

    return NULL; /* no fit */

// #endif
}

static void remove_block(void *bp){
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));

    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    if (SUCC_FREE(bp) != NULL){
        if (PRED_FREE(bp) != NULL){
            PRED_FREE(SUCC_FREE(bp)) = PRED_FREE(bp);
            SUCC_FREE(PRED_FREE(bp)) = SUCC_FREE(bp);
        }else{
            PRED_FREE(SUCC_FREE(bp)) = NULL;
            segregation_list[list] = SUCC_FREE(bp);
        }
    }else{
        if (PRED_FREE(bp) != NULL){
            SUCC_FREE(PRED_FREE(bp)) = NULL;
        }else{
            segregation_list[list] = NULL;
        }
    }

    return;
}

static void insert_block(void *bp, size_t size){
    int list = 0;
    void *search_ptr;
    void *insert_ptr = NULL;

    while ((list < LISTLIMIT - 1) && (size > 1)){
        size >>=1;
        list++;
    }

    search_ptr = segregation_list[list];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))){
        insert_ptr = search_ptr;
        search_ptr = SUCC_FREE(search_ptr);
    }
    
    if (search_ptr != NULL){
        if (insert_ptr != NULL){
            SUCC_FREE(bp) = search_ptr;
            PRED_FREE(bp) = insert_ptr;
            PRED_FREE(search_ptr) = bp;
            SUCC_FREE(insert_ptr) = bp;
        }else{
            SUCC_FREE(bp) = search_ptr;
            PRED_FREE(bp) = NULL;
            PRED_FREE(search_ptr) = bp;
            segregation_list[list] = bp;
        }
    }else{
        if (insert_ptr != NULL){
            SUCC_FREE(bp) = NULL;
            PRED_FREE(bp) = insert_ptr;
            SUCC_FREE(insert_ptr) = bp;
        }else{
            SUCC_FREE(bp) = NULL;
            PRED_FREE(bp) = NULL;
            segregation_list[list] = bp;
        }
    }

    return;
}