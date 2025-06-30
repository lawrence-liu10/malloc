#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#include <stdbool.h>

#include "myMalloc.h"

#define MALLOC_COLOR "MALLOC_DEBUG_COLOR"

static bool check_env;
static bool use_color;

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);
static inline void remove_header_from_freelist(header *header_ptr);
static inline void insert_header_to_freelist(header *header, int insert_idx);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  if (raw_size == 0) {
    return NULL;
  }

  size_t total_size;
  // actual request size including header
  if (raw_size % 8 != 0) {
    total_size = raw_size + (8 - raw_size % 8) + ALLOC_HEADER_SIZE;
  }
  else {
     total_size = raw_size + ALLOC_HEADER_SIZE;
  }


  // minimum allocation is 32 bytes
  if (total_size < sizeof(header)) {
    total_size = sizeof(header);
  }

  header * current = NULL;
  header * freelist = NULL;


  int ilist = (total_size / 8) - 3;
  while (current == NULL) {
    // if ilist > N_LISTS - 1, we need to loop through last list to find a block big enough
    if (ilist >= N_LISTS - 1) {
      freelist = &freelistSentinels[N_LISTS - 1];
      header * block = freelist->next;
      while (block != freelist) {
        if (get_size(block) >= total_size) {
          current = block;
          ilist = N_LISTS - 1;
          break;
        }
        block = block->next;
      }
    }
    else { // ilist is within bounds, just find the next list large enough
      for (; ilist < N_LISTS; ilist++) {
        freelist = &freelistSentinels[ilist];
        if (freelist->next != freelist) {
          current = freelist->next;
          break;
        }
      }
    }

    // START OF CHUNK ALLOCATION
    if (current == NULL) {
      header * new_chunk = allocate_chunk(ARENA_SIZE);
      if (!new_chunk) {
          return NULL;
      }

      header * left_fp = get_left_header(new_chunk);
      header * right_fp = get_right_header(new_chunk);

      int adjacent = (lastFencePost && (get_right_header(lastFencePost) == left_fp));

      if (adjacent) {
        header * last_block = get_left_header(lastFencePost);
        size_t new_size;

        // only coalesce if last block is unallocated
        if (get_state(last_block) == UNALLOCATED) {
          remove_header_from_freelist(last_block);

          //fix sizes
          new_size = get_size(last_block) + ARENA_SIZE;
          set_size(last_block, new_size);
          right_fp->left_size = new_size;
          lastFencePost = right_fp;

          int new_idx = (new_size / 8) - 3;
          if (new_idx >= N_LISTS) {
            new_idx = N_LISTS - 1;
          }
          insert_header_to_freelist(last_block, new_idx);

          current = last_block;
        }
        else { //already allocated, just do fencepost
          header * new_block = lastFencePost;

          new_size = ARENA_SIZE;

          set_state(new_block, UNALLOCATED);
          set_size (new_block, new_size);
          new_block->left_size = get_size(last_block);

          
          right_fp->left_size = new_size;
          lastFencePost = right_fp;

          insert_header_to_freelist(new_block, N_LISTS - 1);
          current = new_block;
        }
      }
      else { //non-adjacent
        insert_header_to_freelist(new_chunk, N_LISTS - 1);
        insert_os_chunk(left_fp);
        lastFencePost = right_fp;
        current = new_chunk;
      }
    }
    // END OF CHUNK ALLOCATION
  }


  // we only split if leftover size is large enough to be another header
  if (get_size(current) >= sizeof(header) + total_size) {
    //split object and initialize header fields
    size_t freeobjsize = get_size(current) - total_size;
    header * allocobj = get_header_from_offset(current, freeobjsize);
    set_size(allocobj, total_size);
    set_state(allocobj, ALLOCATED);
    allocobj->left_size = freeobjsize;

    //adjust left size of the memory RIGHT of our new allocated memory
    header * right_header = get_right_header(allocobj);
    right_header->left_size = total_size;

    // update current block size
    set_size(current, freeobjsize);

    // update right neighbor of current block
    header * cur_right = get_right_header(current);
    cur_right->left_size = freeobjsize;
    // header * left_size_to_adjust = get_right_header(current);
    // left_size_to_adjust->left_size = total_size;
    // set_size(current, freeobjsize);

    // check if we need to move it to a new freelist
    int new_idx = freeobjsize / 8 - 3;
    if (new_idx < ilist) {
      remove_header_from_freelist(current);
      insert_header_to_freelist(current, new_idx);
    }

    return (header *) allocobj->data;
  }
  else {// just remove from free list, leftover too small to be a new header

    // explicitly update right neighbor's left size for unsplit blocks
    header * right_header = get_right_header(current);
    right_header->left_size = get_size(current);

    set_state(current, ALLOCATED);
    remove_header_from_freelist(current);
    return (header *) current->data;
  }
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {

  if (!p) {
    return;
  }


  // get header of memory to deallocate (check for double free before unallocating)
  header * header_to_dealloc = get_header_from_offset((char *)p, -ALLOC_HEADER_SIZE);
  if (get_state(header_to_dealloc) == UNALLOCATED) {
    fprintf(stderr, "Double Free Detected\ntest_double_free: ../myMalloc.c:577: deallocate_object: Assertion `false' failed.\n");
    _exit(1);
  }
  set_state(header_to_dealloc, UNALLOCATED);


  // check if we need to coalesce left and right neighbors
  header * left_header = get_left_header(header_to_dealloc);
  header * right_header = get_right_header(header_to_dealloc);

  int left_state = get_state(left_header);
  int right_state = get_state(right_header);

  // case 1: both neighbors allocated
  if (left_state && right_state) {
    int insert_idx = (get_size(header_to_dealloc) / 8) - 3;
    insert_header_to_freelist(header_to_dealloc, insert_idx);
  }
  // case 2: coalesce right only
  else if (left_state && (!right_state)) {
    remove_header_from_freelist(right_header);
    size_t new_size = get_size(header_to_dealloc) + get_size(right_header);
    set_size(header_to_dealloc, new_size);

    header *right_right = get_right_header(right_header);
    right_right->left_size = new_size;

    int new_idx = (new_size / 8) - 3;
    if (new_idx >= N_LISTS) {
      new_idx = N_LISTS - 1;
    }
    insert_header_to_freelist(header_to_dealloc, new_idx);
  }
  // case 3: coalesce left only
  else if ((!left_state) && right_state) {
    int old_idx = (get_size(left_header) / 8) - 3;
    size_t new_size = get_size(left_header) + get_size(header_to_dealloc);
    set_size(left_header, new_size);
    right_header->left_size = new_size;

    int new_idx = (new_size / 8) - 3;
    if (!(old_idx >= N_LISTS - 1) && (new_idx > old_idx)) {
      remove_header_from_freelist(left_header);
      insert_header_to_freelist(left_header, new_idx);
    }
  }
  // case 4: coalesce both
  else {
    int old_idx = (get_size(left_header) / 8) - 3;
    remove_header_from_freelist(right_header);

    size_t new_size = get_size(left_header) + get_size(header_to_dealloc) + get_size(right_header);
    set_size(left_header, new_size);

    header *right_right = get_right_header(right_header);
    right_right->left_size = new_size;

    int new_idx = (new_size / 8) - 3;
    if (!(old_idx >= N_LISTS - 1) && (new_idx > old_idx)) {
      remove_header_from_freelist(left_header);
      insert_header_to_freelist(left_header, new_idx);
    }
  }
}

/**
 * @brief Helper to remove block from freelist
 *
 * @param p pointer to header to remove
 *
 * @return nothing
 */
static inline void remove_header_from_freelist(header *header_ptr) {

  header_ptr->next->prev = header_ptr->prev;
  header_ptr->prev->next = header_ptr->next;
  header_ptr->prev = NULL;
  header_ptr->next = NULL;

}

/**
 * @brief Helper to insert free memory back where it belongs
 *
 * @param p pointer to header to insert, int index of list to insert to
 *
 * @return nothing
 */
static inline void insert_header_to_freelist(header *header_to_insert, int insert_idx) {

  header * insert_list = NULL;
  if (insert_idx >= N_LISTS - 1) {
    insert_list = &freelistSentinels[N_LISTS - 1];
  }
  else {
    insert_list = &freelistSentinels[insert_idx];
  }

  header_to_insert->next = insert_list->next;
  insert_list->next = header_to_insert;
  header_to_insert->next->prev = header_to_insert;
  header_to_insert->prev = insert_list;
}



/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem;
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}

/**
 * @brief Print just the block's size
 *
 * @param block The block to print
 */
void basic_print(header * block) {
  printf("[%zd] -> ", get_size(block));
}

/**
 * @brief Print just the block's size
 *
 * @param block The block to print
 */
void print_list(header * block) {
	printf("[%zd]\n", get_size(block));
}

/**
 * @brief return a string representing the allocation status
 *
 * @param allocated The allocation status field
 *
 * @return A string representing the allocation status
 */
static inline const char * allocated_to_string(char allocated) {
  switch(allocated) {
    case UNALLOCATED: 
      return "false";
    case ALLOCATED:
      return "true";
    case FENCEPOST:
      return "fencepost";
  }
  assert(false);
}

static bool check_color() {
  if (!check_env) {
    // genenv allows accessing environment varibles
    const char * var = getenv(MALLOC_COLOR);
    use_color = var != NULL && !strcmp(var, "1337_CoLoRs");
    check_env = true;
  }
  return use_color;
}

/**
 * @brief Change the tty color based on the block's allocation status
 *
 * @param block The block to print the allocation status of
 */
static void print_color(header * block) {
  if (!check_color()) {
    return;
  }

  switch(get_state(block)) {
    case UNALLOCATED:
      printf("\033[0;32m");
      break;
    case ALLOCATED:
      printf("\033[0;34m");
      break;
    case FENCEPOST:
      printf("\033[0;33m");
      break;
  }
}

static void clear_color() {
  if (check_color()) {
    printf("\033[0;0m");
  }
}

static inline bool is_sentinel(void * p) {
  for (int i = 0; i < N_LISTS; i++) {
    if (&freelistSentinels[i] == p) {
      return true;
    }
  }
  return false;
}

/**
 * @brief Print the free list pointers if RELATIVE_POINTERS is set to true
 * then print the pointers as an offset from the base of the heap. This allows
 * for determinism in testing. 
 * (due to ASLR https://en.wikipedia.org/wiki/Address_space_layout_randomization#Linux)
 *
 * @param p The pointer to print
 */
void print_pointer(void * p) {
  if (is_sentinel(p)) {
    printf("SENTINEL");
  } else {
    if (RELATIVE_POINTERS) {
      printf("%04zd", p - base);
    } else {
      printf("%p", p);
    }
  }
}

/**
 * @brief Verbose printing of all of the metadata fields of each block
 *
 * @param block The block to print
 */
void print_object(header * block) {
  print_color(block);

  printf("[\n");
  printf("\taddr: ");
  print_pointer(block);
  puts("");
  printf("\tsize: %zd\n", get_size(block) );
  printf("\tleft_size: %zd\n", block->left_size);
  printf("\tallocated: %s\n", allocated_to_string(get_state(block)));
  if (!get_state(block)) {
    printf("\tprev: ");
    print_pointer(block->prev);
    puts("");

    printf("\tnext: ");
    print_pointer(block->next);
    puts("");
  }
  printf("]\n");

  clear_color();
}

/**
 * @brief Simple printer that just prints the allocation status of each block
 *
 * @param block The block to print
 */
void print_status(header * block) {
  print_color(block);
  switch(get_state(block)) {
    case UNALLOCATED:
      printf("[U]");
      break;
    case ALLOCATED:
      printf("[A]");
      break;
    case FENCEPOST:
      printf("[F]");
      break;
  }
  clear_color();
}

/*
static void print_bitmap() {
  printf("bitmap: [");
  for(int i = 0; i < N_LISTS; i++) {
    if ((freelist_bitmap[i >> 3] >> (i & 7)) & 1) {
      printf("\033[32m#\033[0m");
    } else {
      printf("\033[34m_\033[0m");
    }
    if (i % 8 == 7) {
      printf(" ");
    }
  }
  puts("]");
}
*/

/**
 * @brief Print a linked list between two nodes using a provided print function
 *
 * @param pf Function to perform the actual printing
 * @param start Node to start printing at
 * @param end Node to stop printing at
 */
void print_sublist(printFormatter pf, header * start, header * end) {  
  for (header * cur = start; cur != end; cur = cur->next) {
    pf(cur); 
  }
}

/**
 * @brief print the full freelist
 *
 * @param pf Function to perform the header printing
 */
void freelist_print(printFormatter pf) {
  if (!pf) {
    return;
  }

  for (size_t i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    if (freelist->next != freelist) {
      printf("L%zu: ", i);
      print_sublist(pf, freelist->next, freelist);
      puts("");
    }
    fflush(stdout);
  }
}

/**
 * @brief print the boundary tags from each chunk from the OS
 *
 * @param pf Function to perform the header printing
 */
void tags_print(printFormatter pf) {
  if (!pf) {
    return;
  }

  for (size_t i = 0; i < numOsChunks; i++) {
    header * chunk = osChunkList[i];
    pf(chunk);
    for (chunk = get_right_header(chunk);
         get_state(chunk) != FENCEPOST; 
         chunk = get_right_header(chunk)) {
        pf(chunk);
    }
    pf(chunk);
    fflush(stdout);
  }
}
