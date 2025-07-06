#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// We don't actually use this implementation. It's just a reference for
// `persistent_array.rs`.

typedef uint32_t item;

void retainitem(item _item) {}
void releaseitem(item _item) {}

#define LOG2_BRANCHING_FACTOR (1)
#define BRANCHING_FACTOR (1 << LOG2_BRANCHING_FACTOR)

#define ITEMS_PER_LEAF (1)

union node_ref {
  struct branch *branch;
  struct leaf *leaf;
};

struct branch {
  uint64_t refcount;
  union node_ref children[BRANCHING_FACTOR];
};

struct leaf {
  uint64_t refcount;
  item items[ITEMS_PER_LEAF];
};

bool is_null(union node_ref node) {
  // node is maybe not a branch but we gotta check for null somehow
  return node.branch == NULL;
}

struct array {
  uint64_t len;
  uint64_t height;
  struct leaf *tail;
  union node_ref body;
};

struct array new () {
  return (struct array){
      .len = 0,
      .height = -1,
      .tail = NULL,
      .body = NULL,
  };
}

struct node_path {
  uint64_t node_height;
  uint64_t node_number;
};

struct child_node_info {
  uint64_t child_node_height;
  uint64_t child_node_number;
  uint64_t child_index;
};

// INVARIANT: node_height should be not -1
struct child_node_info setnextpath(uint64_t node_height, uint64_t node_number) {
  uint64_t child_index =
      node_number >> ((node_height - 1) * LOG2_BRANCHING_FACTOR);

  uint64_t child_node_number =
      node_number -
      (child_index << ((node_height - 1) * LOG2_BRANCHING_FACTOR));
  uint64_t child_node_height = node_height - 1;

  struct child_node_info child_info = (struct child_node_info){
      .child_node_height = child_node_height,
      .child_node_number = child_node_number,
      .child_index = child_index,
  };

  return child_info;
}

// takes array by reference
item get(struct array array, uint64_t index) {
  if (index >= array.len) {
    fprintf(stderr, "get: array index out of bounds");
    exit(1);
  }

  if (array.height == -1) {
    return array.tail->items[index];
  }

  uint64_t target_node_number = index / ITEMS_PER_LEAF;

  uint64_t tail_node_number = (array.len - 1) / ITEMS_PER_LEAF;

  if (target_node_number == tail_node_number) {
    return array.tail->items[index % ITEMS_PER_LEAF];
  }

  union node_ref current_node = array.body;

  uint64_t current_node_height = array.height;
  uint64_t current_node_number = target_node_number;

  while (current_node_height != 0) {
    struct child_node_info child_info =
        setnextpath(current_node_height, current_node_number);
    current_node_height = child_info.child_node_height;
    current_node_number = child_info.child_node_number;

    current_node = current_node.branch->children[child_info.child_index];
  }

  struct leaf target_leaf = *current_node.leaf;
  return target_leaf.items[index % ITEMS_PER_LEAF];
}

void retainnode(union node_ref node, uint64_t height) {
  if (height == 0) {
    node.leaf->refcount += 1;
  } else {
    node.branch->refcount += 1;
  }
}

// takes node by move (obviously)
void releasenode(union node_ref node, uint64_t height) {
  if (height == 0) {
    struct leaf *leaf = node.leaf;
    leaf->refcount -= 1;
    if (leaf->refcount == 0) {
      for (uint64_t i = 0; i < ITEMS_PER_LEAF; i++) {
        releaseitem(leaf->items[i]);
      }
      free(leaf);
    }
  } else {
    struct branch *branch = node.branch;
    branch->refcount -= 1;
    if (branch->refcount == 0) {
      for (uint64_t i = 0;
           i < BRANCHING_FACTOR && !is_null(branch->children[i]); i++) {
        releasenode(branch->children[i], height - 1);
      }
      free(branch);
    }
  }
}

void retaintail(struct leaf *tail) { tail->refcount += 1; }

// takes tail by move (obviously)
void releasetail(struct leaf *tail, uint64_t tail_len) {
  tail->refcount -= 1;
  if (tail->refcount == 0) {
    for (uint64_t i = 0; i < tail_len; i++) {
      releaseitem(tail->items[i]);
    }
    free(tail);
  }
}

// INVARIANT: len != 0
uint64_t taillen(uint64_t len) { return ((len - 1) % ITEMS_PER_LEAF) + 1; }

void retainarray(struct array array) {
  if (array.len != 0) {
    retaintail(array.tail);
  }
  if (array.len > ITEMS_PER_LEAF) {
    retainnode(array.body, array.height);
  }
}

// takes array by move (obviously)
void releasearray(struct array array) {
  if (array.len != 0) {
    releasetail(array.tail, taillen(array.len));
  }
  if (array.len > ITEMS_PER_LEAF) {
    releasenode(array.body, array.height);
  }
}

// takes leaf by move
struct leaf *obtainuniqueleaf(struct leaf *leaf) {
  if (leaf->refcount == 1) {
    return leaf;
  }

  struct leaf *result = (struct leaf *)calloc(1, sizeof(struct leaf));
  result->refcount = 1;
  memcpy(result->items, leaf->items, sizeof(leaf->items));

  for (uint64_t i = 0; i < ITEMS_PER_LEAF; i++) {
    retainitem(leaf->items[i]);
  }

  leaf->refcount -= 1;

  return result;
}

// takes branch by move
struct branch *obtainuniquebranch(struct branch *branch, uint64_t height) {
  if (branch->refcount == 1) {
    return branch;
  }

  struct branch *result = (struct branch *)calloc(1, sizeof(struct branch));
  result->refcount = 1;
  memcpy(result->children, branch->children, sizeof(branch->children));

  // might not be a branch, but still gotta check for null
  for (uint64_t i = 0; i < BRANCHING_FACTOR && !is_null(branch->children[i]);
       i++) {
    retainnode(branch->children[i], height - 1);
  }

  branch->refcount -= 1;

  return result;
}

// takes tail by move
struct leaf *obtainuniquetail(struct leaf *tail, uint64_t tail_len) {
  if (tail->refcount == 1) {
    return tail;
  }

  struct leaf *result = (struct leaf *)calloc(1, sizeof(struct leaf));
  result->refcount = 1;
  memcpy(result->items, tail->items, sizeof(item) * tail_len);

  for (uint64_t retain_i = 0; retain_i < tail_len; retain_i++) {
    retainitem(tail->items[retain_i]);
  }

  tail->refcount -= 1;

  return result;
}

// takes tail by move
struct leaf *settail(struct leaf *tail, uint64_t tail_len,
                     uint64_t index_in_tail, item item) {
  struct leaf *result = obtainuniquetail(tail, tail_len);

  releaseitem(result->items[index_in_tail]);
  result->items[index_in_tail] = item;

  return result;
}

// takes node by move
union node_ref setnode(union node_ref node, uint64_t node_height,
                       uint64_t node_number, uint64_t index_in_child,
                       item item) {
  if (node_height == 0) {
    struct leaf *result = obtainuniqueleaf(node.leaf);

    releaseitem(result->items[index_in_child]);

    result->items[index_in_child] = item;

    return (union node_ref){.leaf = result};
  }

  struct branch *result = obtainuniquebranch(node.branch, node_height);

  struct child_node_info child_info = setnextpath(node_height, node_number);

  union node_ref child_node = setnode(
      result->children[child_info.child_index], child_info.child_node_height,
      child_info.child_node_number, index_in_child, item);

  result->children[child_info.child_index] = child_node;

  return (union node_ref){.branch = result};
}

// takes array by move
struct array set(struct array old_array, uint64_t index, item item) {
  if (index >= array.len) {
    fprintf(stderr, "set: array index out of bounds");
    exit(1);
  }

  struct array array = obtainunique(old_array, index)

  uint64_t target_node_number = index / ITEMS_PER_LEAF;

  uint64_t tail_node_number = (array.len - 1) / ITEMS_PER_LEAF;

  // set occurs in tail
  if (target_node_number == tail_node_number) {
    uint64_t tail_len = taillen(array.len);
    uint64_t index_in_tail = index % ITEMS_PER_LEAF;

    // moves array.tail
    struct leaf *new_tail = settail(array.tail, tail_len, index_in_tail, item);

    // moves array.body
    return (struct array){
        .len = array.len,
        .height = array.height,
        .tail = new_tail,
        .body = array.body,
    };
  }

  // otherwise, set occurs in body
  uint64_t index_in_child = index % ITEMS_PER_LEAF;

  // moves array.body
  union node_ref new_body = setnode(array.body, array.height,
                                    target_node_number, index_in_child, item);

  // moves array.tail
  return (struct array){
      .len = array.len,
      .height = array.height,
      .tail = array.tail,
      .body = new_body,
  };
}

uint64_t len(struct array array) { return array.len; }

// INVARIANT: tail is not full
struct leaf *pushtail(struct leaf *tail, uint64_t tail_len, item item) {
  struct leaf *result = obtainuniquetail(tail, tail_len);

  result->items[tail_len] = item;

  return result;
}

// INVARIANT: node_height >= 1
// takes tail and branch by move
struct branch *puttail(struct branch *branch, uint64_t node_height,
                       uint64_t node_number, struct leaf *tail) {
  struct branch *result = obtainuniquebranch(branch, node_height);
  if (node_height == 1) {
    // moves tail
    result->children[node_number] = (union node_ref){.leaf = tail};
    return result;
  }

  struct child_node_info child_info = setnextpath(node_height, node_number);

  // create sub-child if it doesn't exist yet
  if (is_null(result->children[child_info.child_index])) {
    result->children[child_info.child_index].branch =
        calloc(1, sizeof(struct branch));
    result->children[child_info.child_index].branch->refcount = 1;
  }

  // moves tail
  struct branch *new_child =
      puttail(result->children[child_info.child_index].branch,
              child_info.child_node_height, child_info.child_node_number, tail);

  result->children[child_info.child_index].branch = new_child;

  return result;
}

// takes array by move
struct array push(struct array array, item item) {
  // case: array empty
  if (array.len == 0) {
    struct leaf *tail = calloc(1, sizeof(struct leaf));
    tail->refcount = 1;
    tail->items[0] = item;

    return (struct array){
        .len = 1,
        .height = -1,
        .tail = tail,
        .body = NULL,
    };
  }

  // case: tail not full
  // if you really want to, this also works
  // let tail_len = array.len % ITEMS_PRE_LEAF;
  uint64_t tail_len = taillen(array.len);
  if (tail_len != ITEMS_PER_LEAF) {
    // moves array.tail
    struct leaf *new_tail = pushtail(array.tail, tail_len, item);

    // moves array.body
    return (struct array){
        .len = array.len + 1,
        .height = array.height,
        .tail = new_tail,
        .body = array.body,
    };
  }

  // case: tail full, body empty
  if (array.len == ITEMS_PER_LEAF) {
    struct leaf *new_tail = calloc(1, sizeof(struct leaf));
    new_tail->refcount = 1;
    new_tail->items[0] = item;

    // moves array.tail
    return (struct array){
        .len = array.len + 1,
        .height = 0,
        .tail = new_tail,
        .body = (union node_ref){.leaf = array.tail},
    };
  }

  // case: tail full, body full
  if (array.len - ITEMS_PER_LEAF ==
      ITEMS_PER_LEAF * (1 << (array.height * LOG2_BRANCHING_FACTOR))) {
    struct branch *new_body = calloc(1, sizeof(struct branch));
    new_body->refcount = 1;
    new_body->children[0] = array.body; // moves array.body

    uint64_t tail_node_number = 1 << (array.height * LOG2_BRANCHING_FACTOR);

    // moves array.tail
    new_body =
        puttail(new_body, array.height + 1, tail_node_number, array.tail);

    struct leaf *new_tail = calloc(1, sizeof(struct leaf));
    new_tail->refcount = 1;
    new_tail->items[0] = item;

    return (struct array){
        .len = array.len + 1,
        .height = array.height + 1,
        .tail = new_tail,
        .body = new_body,
    };
  }

  // case: tail full, body partially full
  uint64_t target_node_number = (array.len - ITEMS_PER_LEAF) / ITEMS_PER_LEAF;

  // moves array.body
  struct branch *result = obtainuniquebranch(array.body.branch, array.height);

  // moves array.tail
  struct branch *new_body =
      puttail(result, array.height, target_node_number, array.tail);

  struct leaf *new_tail = calloc(1, sizeof(struct leaf));
  new_tail->refcount = 1;
  new_tail->items[0] = item;

  return (struct array){
      .len = array.len + 1,
      .height = array.height,
      .tail = new_tail,
      .body = new_body,
  };
}

struct poptail_ret {
  item item;
  struct leaf *new_tail;
};

// INVARIANT: tail_len >= 2
// takes tail by move
struct poptail_ret poptail(struct leaf *tail, uint64_t tail_len) {
  struct leaf *result = obtainuniquetail(tail, tail_len);

  item item = result->items[tail_len - 1];
  // not needed for performance, but needed for sanity
  memset(&result->items[tail_len - 1], 0, sizeof(item));

  return (struct poptail_ret){
      .item = item,
      .new_tail = result,
  };
}

struct popnode_ret {
  struct leaf *new_tail;
  struct branch *new_branch;
};

// new_branch == NULL might happen
// takse branch by move
struct popnode_ret popnode(struct branch *branch, uint64_t node_height,
                           uint64_t node_number) {
  struct branch *result = obtainuniquebranch(branch, node_height);

  if (node_height == 1) {
    struct leaf *new_tail = result->children[node_number].leaf;
    result->children[node_number].leaf = NULL;

    // our only child just died, kill ourselves
    if (node_number == 0) {
      free(result);

      return (struct popnode_ret){
          .new_tail = new_tail,
          .new_branch = NULL,
      };
    }

    return (struct popnode_ret){
        .new_tail = new_tail,
        .new_branch = result,
    };
  }

  struct child_node_info child_info = setnextpath(node_height, node_number);

  struct popnode_ret popnode_ret =
      popnode(result->children[child_info.child_index].branch,
              child_info.child_node_height, child_info.child_node_number);

  // all our desendents are dead, kill ourselves
  if (node_number == 0) {
    free(result);

    return (struct popnode_ret){
        .new_tail = popnode_ret.new_tail,
        .new_branch = NULL,
    };
  }

  result->children[child_info.child_index].branch = popnode_ret.new_branch;

  return (struct popnode_ret){
      .new_tail = popnode_ret.new_tail,
      .new_branch = result,
  };
}

struct pop_ret {
  item item;
  struct array new_array;
};

// takes array by move
struct pop_ret pop(struct array array) {
  // case: empty
  if (array.len == 0) {
    fprintf(stderr, "don't negate a byte u dummy");
    exit(1);
  }

  // case: len 1
  if (array.len == 1) {
    // moves array.tail
    struct leaf *result_tail = obtainuniquetail(array.tail, 1);
    item item = result_tail->items[0];

    free(result_tail);

    struct array new_array = (struct array){
        .len = 0,
        .height = -1,
        .tail = NULL,
        .body = NULL,
    };

    return (struct pop_ret){
        .item = item,
        .new_array = new_array,
    };
  }

  uint64_t tail_len = taillen(array.len);

  // case: tail not len 1
  if (tail_len != 1) {
    // moves array.tail
    struct poptail_ret poptail_ret = poptail(array.tail, tail_len);

    // moves array.body
    struct array new_array = (struct array){
        .len = array.len - 1,
        .height = array.height,
        .tail = poptail_ret.new_tail,
        .body = array.body,
    };

    return (struct pop_ret){
        .item = poptail_ret.item,
        .new_array = new_array,
    };
  }

  // case: popping leaves body empty
  if (array.len == ITEMS_PER_LEAF + 1) {
    // moves array.tail
    struct leaf *result_tail = obtainuniquetail(array.tail, 1);
    item item = result_tail->items[0];

    free(result_tail);

    // moves array.body
    struct array new_array = (struct array){
        .len = array.len - 1,
        .height = -1,
        .tail = array.body.leaf,
        .body = NULL,
    };

    return (struct pop_ret){
        .item = item,
        .new_array = new_array,
    };
  }

  // case: everything else
  // moves array.tail
  struct leaf *result_tail = obtainuniquetail(array.tail, 1);
  item item = result_tail->items[0];

  free(result_tail);

  uint64_t new_array_len = array.len - 1;
  uint64_t target_node_number = (new_array_len - 1) / ITEMS_PER_LEAF;

  // move array.body
  struct popnode_ret popnode_ret =
      popnode(array.body.branch, array.height, target_node_number);

  // if we have only one grandchild, kill our child and promote our
  // grandchild
  if (is_null(popnode_ret.new_branch->children[1])) {
    union node_ref grandchild = popnode_ret.new_branch->children[0];
    struct array new_array = (struct array){
        .len = array.len - 1,
        .height = array.height - 1,
        .tail = popnode_ret.new_tail,
        .body = grandchild,
    };

    free(popnode_ret.new_branch);

    return (struct pop_ret){
        .item = item,
        .new_array = new_array,
    };
  }

  struct array new_array = (struct array){
      .len = array.len - 1,
      .height = array.height,
      .tail = popnode_ret.new_tail,
      .body = popnode_ret.new_branch,
  };

  return (struct pop_ret){
      .item = item,
      .new_array = new_array,
  };
}

void print_tail(struct leaf *tail, uint64_t tail_len) {
  printf("tail, rc : %lu | ", tail->refcount);
  for (int i = 0; i < tail_len; i++) {
    printf("%d ", tail->items[i]);
  }
  printf("\n");
}

void print_node(union node_ref node, uint64_t height, uint64_t node_number,
                uint64_t original_height) {
  if (height == 0) {
    for (int i = height; i < original_height; i++) {
      printf(" ");
    }
    printf("#%lu, rc : %lu | ", node_number, node.leaf->refcount);
    for (int i = 0; i < ITEMS_PER_LEAF; i++) {
      printf("%d ", node.leaf->items[i]);
    }
    printf("\n");
  } else {
    for (int i = height; i < original_height; i++) {
      printf(" ");
    }
    printf("branch height %lu, #%lu, rc: %lu\n", height, node_number,
           node.branch->refcount);
    for (int i = 0; i < BRANCHING_FACTOR && !is_null(node.branch->children[i]);
         i++) {
      print_node(node.branch->children[i], height - 1,
                 node_number * BRANCHING_FACTOR + i, original_height);
    }
  }
}

void print_array(struct array array) {
  printf("len: %lu\n", array.len);
  printf("height: %ld\n", (int64_t)array.height);
  if (array.len != 0) {
    print_tail(array.tail, taillen(array.len));
  }
  if (array.height != -1) {
    print_node(array.body, array.height, 0, array.height);
  }
}

const uint64_t MAX_SIZE = 50;

void test_push() {
  printf("running test_push\n");
  struct array a = new ();
  for (int i = 0; i < MAX_SIZE; i++) {
    a = push(a, i);
  }

  releasearray(a);
}

void test_pushmany() {
  printf("running test_pushmany\n");
  struct array arrays[MAX_SIZE];

  struct array a = new ();
  for (int i = 0; i < MAX_SIZE; i++) {
    a = push(a, i);
    retainarray(a);
    arrays[i] = a;
  }

  releasearray(a);

  for (int i = 0; i < MAX_SIZE; i++) {
    releasearray(arrays[i]);
  }
}

struct array get_array(uint64_t len) {
  struct array a = new ();
  for (int i = 0; i < len; i++) {
    a = push(a, i);
  }

  return a;
}

void test_get() {
  printf("running test_get\n");
  for (int i = 0; i < MAX_SIZE; i++) {
    struct array a = get_array(i);
    for (int j = 0; j < i; j++) {
      assert(get(a, j) == j);
    }
    releasearray(a);
  }
}

void test_pop() {
  printf("running test_pop\n");
  struct array a = get_array(MAX_SIZE);
  for (int i = MAX_SIZE - 1; i >= 0; i--) {
    struct pop_ret pop_ret = pop(a);
    assert(pop_ret.item == i);
    a = pop_ret.new_array;
  }

  releasearray(a);
}

void test_set() {
  printf("running test_set\n");
  for (int i = 0; i < MAX_SIZE; i++) {
    struct array a = get_array(i);
    for (int j = 0; j < i; j++) {
      retainarray(a);
      struct array b = set(a, j, 0);
      assert(get(b, j) == 0);
      releasearray(b);
    }
    releasearray(a);
  }
}

void test_set2() {
  printf("running test_set2\n");
  struct array arrays[MAX_SIZE];

  struct array a = new ();
  for (int i = 0; i < MAX_SIZE; i++) {
    retainarray(a);
    arrays[i] = a;
    a = push(a, i);
  }
  releasearray(a);

  // set every even index array to 0
  for (int i = 0; i < MAX_SIZE; i += 2) {
    for (int j = 0; j < i; j++) {
      arrays[i] = set(arrays[i], j, 0);
    }
  }

  // check that every odd index array is unmodified
  for (int i = 1; i < MAX_SIZE; i += 2) {
    for (int j = 0; j < i; j++) {
      assert(get(arrays[i], j) == j);
    }
  }

  // check that every even index array is all 0
  for (int i = 0; i < MAX_SIZE; i += 2) {
    for (int j = 0; j < i; j++) {
      assert(get(arrays[i], j) == 0);
    }
  }

  for (int i = 0; i < MAX_SIZE; i++) {
    releasearray(arrays[i]);
  }
}

int main() {
  test_push();
  test_pushmany();
  test_get();
  test_pop();
  test_set();
  test_set2();
}
