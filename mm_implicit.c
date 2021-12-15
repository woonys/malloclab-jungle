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
    "3",
    /* First member's full name */
    "Jaewoon Kim",
    /* First member's email address */
    "wodns1324@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 8의 배수로 alignment

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // 무시


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 /* word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes): 초기 가용블록과 힙 확장을 위한 기본 크기: 12바이트*/ 

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // x>y가 참이면 x, 거짓이면 y

/* Pack a size and allocated bit into a word */
// PACK 매크로: 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값 리턴
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
// bp(현재 블록 포인터)로 현재 블록의 header 위치와 footer 위치 반환
#define HDRP(bp) ((char *)(bp) - WSIZE) // 헤더 사이즈 하나 빼면 payload 가리키던 곳에서 한 칸 앞으로 가서 헤더가 나옴.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
// 다음과 이전 블록 포인터 반환

// 다음 블록 bp 위치 반환(bp + 현재 블록의 크기)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 이전 블록 bp 위치 반환(bp - 이전 블록의 크기)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//Declaration(선언)
static void *heap_listp;
static void *next_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) { // heap_listp가 힙의 최댓값 이상을 요청하면 fail
        return -1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);
    next_listp = (char *)heap_listp;
    /* Extend the empth heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/* extend heap 사용할 경우
1) 힙이 초기화될 때
2) mm_malloc이 적당한 fit을 찾지 못했을 때
*/

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    //Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; //words가 홀수면 +1해서 공간 할당
    if ((long)(bp =mem_sbrk(size)) == -1) {
        return NULL;
    }

    //Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /*
    extend_heap 블록 너머에 오지 않도록 배치한 블록 다음 공간을 블록이라 가정하고 epilogue header 배치 (실제로는 존재 X
    */

   // coalesce if the previous block was free
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    
    size_t a_size;
    size_t extend_size;
    char *bp;

    // ignore spurious requests
    if (size == 0) {
        return NULL;
    }

    // Adjust block size to include overhead and alignment reqs
    if (size <= DSIZE) {
        // 2words 이하 사이즈면 4 워드로 할당 요청해라 (header에 1word, footer 1word)
        a_size = 2*DSIZE;

    }
    else {
        //할당 요청 용량이 2 word를 초과하면 충분한 8바이트 배수 용량을 할당해라
        a_size = DSIZE *((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    //search the free list for a fit
    if ((bp = find_fit(a_size))!= NULL) {
        place(bp, a_size);
        return bp;
    }

    //No fir found. Get more memory and place the block
    extend_size = MAX(a_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, a_size);
    return bp;
}

static void *find_fit(size_t a_size) {
    void *bp = next_listp;
    
    for (bp = (char *)NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) > 0; bp= NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (a_size <= GET_SIZE(HDRP(bp)))) {
            next_listp = bp;
            return bp;   
        }
    }
    bp = heap_listp;
    while (bp < next_listp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= a_size) {
            next_listp = bp;
            return bp;
        }
    }
    return NULL;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);

}

static void *coalesce(void *bp) // 앞뒤 블록 확인해 합치기
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1: 현재 블록을 기준으로 앞뒤 블록 다 alloc되어 있다면 */
    if (prev_alloc && next_alloc) { 
        next_listp = bp; // 여기에 next값이 들어가야 함..! 여기에 할당하니까 여기 뒤부터 돌아야 함.
        return bp;
    }

    /* case 2: 앞쪽은 alloc 되어 있고 뒤쪽은 free */
    else if (prev_alloc && !next_alloc) { 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* case 3: 앞쪽은 free 되어 있고 뒤쪽은 alloc */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* case 4: 앞뒤 둘다 free */
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    next_listp = bp;
    return bp;
}

static void place(void *bp, size_t adjusted_size) {
    size_t current_size = GET_SIZE(HDRP(bp));

    if ((current_size - adjusted_size) >= (2*(DSIZE))) {
        // 요청 용량만큼 블록 배치
        PUT(HDRP(bp), PACK(adjusted_size, 1));
        PUT(FTRP(bp), PACK(adjusted_size, 1));

        bp = NEXT_BLKP(bp);
        //남은 블록에 header, footer 배치
        PUT(HDRP(bp), PACK(current_size - adjusted_size, 0));
        PUT(FTRP(bp), PACK(current_size - adjusted_size, 0));
    }

    else {
        //csize와 asize 차이가 네 칸(16바이트) 보다 작다면 해당 블록을 통쨰로 사용한다
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *old_bp = bp;
    void *new_bp;
    size_t copySize;
    
    new_bp = mm_malloc(size);
    if (new_bp == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(old_bp));
    if (size < copySize)
      copySize = size;
    memcpy(new_bp, old_bp, copySize); // 메모리 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 copysize만큼의 문자를 new_bp로 복사)
    mm_free(old_bp);
    return new_bp;

    // 위랑 아래랑 무슨 차이?
}














