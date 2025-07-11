#include <stddef.h>

struct list {
    unsigned head;
    struct list *tail;
};

struct list *reverse(struct list *l) {
    struct list *t, *r = NULL;

    while (l) {
        t = l;
        l = l->tail;
        t->tail = r;
        r = t;
    }

    return r;
}
