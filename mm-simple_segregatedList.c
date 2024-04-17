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
    "11-team",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE           4        /* Word and header/footer size (bytes) */
#define DSIZE           8        /* Double word size (bytes) */
#define CHUNKSIZE       (1<<12)  /* Extend heap by this amonut */
#define INITCHUNKSIZE   (1<<6)
#define LISTLIMIT       20
#define REALLOC_BUFFER  (1<<7)

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */

#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Given block ptr bp, copute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))
#define NEXT_PTR(ptr)   ((char *)(ptr)) 
#define PREV_PTR(ptr)   ((char *)(ptr) + WSIZE) 

#define NEXT(ptr)       (*(char **)(ptr))
#define PREV(ptr)       (*(char **)(PREV_PTR(ptr)))

/* Private global variables */
char *heap_listp = 0;
void *segregated_free_lists[LISTLIMIT];
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *bp, size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int i;
    for (i = 0; i < LISTLIMIT ; i++)
    {
        segregated_free_lists[i] = NULL;
    }

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                                     /*Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));            /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));            /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));                /* Epilogue header */
    heap_listp += (2*WSIZE);

    // if (extend_heap(4) == NULL)
    //     return -1;
    /* Extend the empty heap with a free blcok of CHUNKSIZE bytes */
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words +1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));        /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));        /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));/* New epilogue header */
    insert_node(bp,size);

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void insert_node(void *ptr, size_t size)
{
    int idx = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;

    while ((idx < LISTLIMIT -1) && (size > 1))                               //알맞은 가용리스트 찾기
    {                                                                        //인덱스가 가용리스트의 개수보다 작고 사이즈가 1이 될 때까지 반복문을 수행
        size >>= 1;                                                          //반복 수행마다 사이즈를 2로 나눈다
        idx++;                                                               //반복 수행마다 idx를 1씩 증가 시킴
    }

    search_ptr = segregated_free_lists[idx];                                 //찾은 가용리스트의 처음 주소를 search_ptr에 할당.

    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr))))      //리스트에서 메모리 블럭 삽입 위치 찾기
    {
        insert_ptr = search_ptr;                                             //삽입할 위치는 search_ptr 할당
        search_ptr = NEXT(search_ptr);                                       //search_ptr은 다음 블럭을 탐색
    }

    if (search_ptr != NULL)                                                  //다음 블럭이 있을 경우
    {
        if (insert_ptr != NULL)                                              //이전 블럭이 있을 경우
        {
            SET_PTR(NEXT_PTR(ptr), search_ptr);                              //삽입 블럭의 다음 블럭으로 search_ptr 저장
            SET_PTR(PREV_PTR(search_ptr), ptr);                              //다음 블럭의 이전 블럭으로 ptr 저장
            SET_PTR(PREV_PTR(ptr), insert_ptr);                              //삽입 블럭의 이전 블럭으로 insert_ptr 저장
            SET_PTR(NEXT_PTR(insert_ptr), ptr);                              //이전 블럭의 다음 블럭으로 ptr 저장
        }
        else                                                                 //이전 블럭이 없을 경우(리스트에서 가장 작은 블럭을 삽입하는 경우)
        {
            SET_PTR(NEXT_PTR(ptr), search_ptr);                              //삽입 블럭의 다음 블럭으로 search_ptr 저장
            SET_PTR(PREV_PTR(search_ptr), ptr);                              //다음 블럭의 이전 블럭으로 ptr 저장
            SET_PTR(PREV_PTR(ptr), NULL);                                    //삽입 블럭의 이전 블럭으로 NULL 저장
            segregated_free_lists[idx] = ptr;                                //가용리스트의 첫번째 주소값 배열에 ptr 저장
        }
    }
    else                                                                     //다음 블럭이 없을 경우
    {
        if (insert_ptr != NULL)                                              //이전 블럭이 있을 경우
        {
            SET_PTR(NEXT_PTR(ptr), NULL);                                    //삽입 블럭의 다음 블럭은 NULL(없다)
            SET_PTR(PREV_PTR(ptr), insert_ptr);                              //삽입 블럭의 이전 블럭으로 insert_ptr 저장
            SET_PTR(NEXT_PTR(insert_ptr), ptr);                              //이전 블럭의 다음 블럭으로 ptr 저장
        }
        else                                                                 //이전 블록도 다음 블록도 없을 경우(리스트가 빈 경우)
        {
            SET_PTR(NEXT_PTR(ptr), NULL);                                    //삽입 블럭의 다음 블럭은 NULL
            SET_PTR(PREV_PTR(ptr), NULL);                                    //삽입 블럭의 이전 블럭은 NULL
            segregated_free_lists[idx] = ptr;                                //가용리스트의 첫번째 주소값 배열에 ptr 저장
        }
    }
    return;
}

static void delete_node(void *ptr)
{
    int idx = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    while ((idx < LISTLIMIT -1) && (size > 1))                               //알맞은 가용리스트 찾기
    {
        size >>= 1;
        idx++;
    }

    if (NEXT(ptr) != NULL)                                                   //다음 블럭이 있을 경우
    {
        if (PREV(ptr) != NULL)                                               //이전 블럭도 있을 경우
        {
            SET_PTR(PREV_PTR(NEXT(ptr)), PREV(ptr));                         //다음 블럭의 이전 블럭을 삭제 블럭의 이전 블럭으로 저장
            SET_PTR(NEXT_PTR(PREV(ptr)), NEXT(ptr));                         //이전 블럭의 다음 블럭을 삭제 블럭의 다음 블럭으로 저장
        }
        else                                                                 //이전 블럭이 없을 경우 (삭제 블럭이 리스트의 첫번째 블럭)
        {
            SET_PTR(PREV_PTR(NEXT(ptr)), NULL);                              //다음 블럭의 이전블럭을 NULL로 저장
            segregated_free_lists[idx] = NEXT(ptr);                          //리스트의 첫번째 블럭으로 삭제 블럭의 다음 블럭을 저장
        }
    }
    else                                                                     //다음 블럭이 없을 경우
    {
        if (PREV(ptr) != NULL)                                               //이전 블럭이 있을 경우
            SET_PTR(NEXT_PTR(PREV(ptr)), NULL);                              //이전 블럭의 다음 블럭을 NULL로 저장
        else                                                                 //이전 블럭도 없을 경우 (리스트에 삭제 블럭 한개만 있을 경우)
            segregated_free_lists[idx] = NULL;                               //리스트에는 블럭이 하나도 없도록 NULL
    }
    return;
}

static void *find_fit(size_t asize)
{
    char *bp;

    int idx = 0;
    size_t searchsize = asize;

    while (idx < LISTLIMIT)
    {
        if ((idx == LISTLIMIT -1) || ((searchsize <= 1) && (segregated_free_lists[idx] != NULL))) //(가용리스트를 다 돌거나 or 찾으려는 사이즈가 1보다 작거나 같을 때) and (가용리스트에 블럭이 있을 때)
        {
            bp =segregated_free_lists[idx];                                                       //블럭 주소는 가용리스트의 첫번째 주소

            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp)))))                                //다음 가용리스트가 있고, 사이즈가 현재 가용블럭의 사이즈 보다 크면 반복문 수행
            {
                bp = NEXT(bp);                                                                    //다음 가용블럭 탐색
            }
            if (bp != NULL)                                                                       //알맞은 가용블럭을 찾으면 해당 블럭 리턴
                return bp;
        }

        searchsize >>= 1;                                                                         //없을  경우 다음 가용 리스트를 탐색
        idx ++;
    }
    return NULL;                                                                                  //가용 리스트에 적절한 블럭이 없을 경우 NULL을 리턴
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));                                                            //가용 블럭의 사이즈
    delete_node(bp);                                                                              //가용 리스트에서 블럭 제거
    if ((csize - asize) >= (2*DSIZE)){                                                            //메모리를 저장하고 남은 크기가 16바이트보다 크다면.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));                                                      //블럭 분할 후,
        insert_node(bp,(csize-asize));                                                            //가용리스트에 삽입
    }

    else {                                                                                        //16바이트보다 작다면 가용블럭 통째로 사용
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    size_t asize; 
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else    
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    insert_node(bp, size);                                     //블럭 반환 시 가용리스트에 블럭 삽입

    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {                            
        return bp;
    }
    else if (prev_alloc && !next_alloc) {                       //현재 블럭과 다음 블럭이 가용상태일때
        delete_node(bp);                                        
        delete_node(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));                  
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {                       //현재 블럭과 이전 블럭이 가용상태일때
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else                                                        //현재 블럭과 다음 블럭, 이전 블럭이 가용상태일때
    {
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    insert_node(bp, size);                                      //조건문을 돌고 나와서 가용리스트에 블럭 삽입
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldbp = bp;
    void *newbp;
    size_t copySize;
    
    newbp = mm_malloc(size);
    if (newbp == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldbp));
    if (size < copySize)
      copySize = size;
    memcpy(newbp, oldbp, copySize);
    mm_free(oldbp);
    return newbp;
}