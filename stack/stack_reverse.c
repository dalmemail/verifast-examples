#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/*@

inductive ints = ints_nil | ints_cons(int, ints);

fixpoint int ints_head(ints values) {
    switch (values) {
        case ints_nil: return 0;
        case ints_cons(value, values0): return value;
    }
}

fixpoint ints ints_tail(ints values) {
    switch (values) {
        case ints_nil: return ints_nil;
        case ints_cons(value, values0): return values0;
    }
}

predicate nodes(struct node *node, ints values) =
    node == 0 ?
        values == ints_nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& values == ints_cons(value, values0);

predicate stack(struct stack *stack, ints values) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, values);

@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, ints_nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    //@ close nodes(0, ints_nil);
    //@ close stack(stack, ints_nil);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, ints_cons(value, values));
{
    //@ open stack(stack, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, ints_cons(value, values));
    //@ close stack(stack, ints_cons(value, values));
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?values) &*& values != ints_nil;
    //@ ensures stack(stack, ints_tail(values)) &*& result == ints_head(values);
{
    //@ open stack(stack, values);
    struct node *head = stack->head;
    //@ open nodes(head, values);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, ints_tail(values));
    return result;
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, ints_nil);
    //@ ensures true;
{
    //@ open stack(stack, ints_nil);
    //@ open nodes(_, _);
    free(stack);
}

/*@
    fixpoint ints reverse_values_aux(ints values, ints aux)
    {
        switch (values) {
            case ints_nil:
                return aux;
            case ints_cons(value, values0):
                return reverse_values_aux(values0, ints_cons(value, aux));
        }
    }

    fixpoint ints reverse_values(ints values)
    {
        return reverse_values_aux(values, ints_nil);
    }
@*/

void stack_reverse(struct stack *stack)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, reverse_values(values));
{
    //@ open stack(stack, values);
    //@ open nodes(_, _);
    // if stack has at least 2 elements (otherwise is already reversed)
    struct node *head = stack->head;
    // we need to put it into two separate ifs so that verifast can deduce
    // that reverse_values(values) == values
    if (stack->head == 0)
    {
        //@ close nodes(head, reverse_values(values));
        //@ close stack(stack, reverse_values(values));
        return;
    }

    // we need this variable anyway but we need to do it here because
    // verifast doesn't allow dereferences on open and close annotations
    struct node *next = stack->head->next;
    if (stack->head->next == 0)
    {
        //@ open nodes(next, _);
        //@ close nodes(next, ints_tail(reverse_values(values)));
        //@ close nodes(head, reverse_values(values));
        //@ close stack(stack, reverse_values(values));
        return;
    }

    head->next = 0;
    int value = head->value;
    //@ close nodes(0, ints_nil);
    //@ close nodes(head, ints_cons(value, ints_nil));
    while (next != 0)
        //@ invariant nodes(head, ?reversed_values_so_far) &*& nodes(next, ?not_reversed_yet) &*& reverse_values(values) == reverse_values_aux(not_reversed_yet, reversed_values_so_far);
    {
        //@ open nodes(next, not_reversed_yet);
        struct node *aux = next->next;
        next->next = head;
        // we can't dereference anything on close annotations...
        value = next->value;

        head = next;
        next = aux;
        //@ close nodes(head, ints_cons(value, reversed_values_so_far));
    }
    stack->head = head;
    //@ open nodes(next, _);
    //@ close stack(stack, reverse_values(values));
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    int result1 = stack_pop(s);
    assert(result1 == 20);
    int result2 = stack_pop(s);
    assert(result2 == 10);
    stack_dispose(s);
    return 0;
}
