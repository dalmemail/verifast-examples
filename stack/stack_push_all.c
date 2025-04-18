#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/*@

predicate nodes(struct node *node, int count) =
    node == 0 ? count == 0 : 0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(head, count);

@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    //@ close nodes(0, 0);
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count + 1);
{
    //@ open stack(stack, count);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, count + 1);
    //@ close stack(stack, count + 1);
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?count) &*& 0 < count;
    //@ ensures stack(stack, count - 1);
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ open nodes(head, count);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, count - 1);
    return result;
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, 0);
    //@ ensures true;
{
    //@ open stack(stack, 0);
    //@ open nodes(_, _);
    free(stack);
}

/*@

predicate lseg(struct node *first, struct node *last, int count) =
    (first == last) ? count == 0 : 0 < count &*& first != 0 &*& malloc_block_node(first) &*& first->next |-> ?next &*& first->value |-> ?value &*& lseg(next, last, count - 1);
    
lemma void nodes_to_lseg(struct node *first)
    requires nodes(first, ?count);
    ensures lseg(first, 0, count);
{
    open nodes(first, count);
    if (count > 0)
    {
        nodes_to_lseg(first->next);
    }
    close lseg(first, 0, count);
}

lemma void lseg_tail_add(struct node *first)
    requires lseg(first, ?last, ?count) &*& malloc_block_node(last) &*& last->next |-> ?next &*& last->value |-> ?value &*& lseg(next, 0, ?count0) &*& last != 0;
    ensures lseg(first, next, count + 1) &*& lseg(next, 0, count0);
{
    open lseg(first, last, count);
    if (first == last) {
        close lseg(next, next, 0);
    } else {
        lseg_tail_add(first->next);
    }
    open lseg(next, 0, count0);
    close lseg(next, 0, count0);
    close lseg(first, next, count + 1);
}

lemma void lseg_to_nodes(struct node *first)
    requires lseg(first, 0, ?count);
    ensures nodes(first, count);
{
    open lseg(first, 0, count);
    if (first != 0)
    {
        lseg_to_nodes(first->next);
    }
    close nodes(first, count);
}

@*/

int stack_get_count(struct stack *stack)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count) &*& result == count;
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    struct node *n = head;
    int i = 0;
    //@ close lseg(head, head, 0);
    //@ nodes_to_lseg(n);
    while (n != 0)
        //@ invariant lseg(head, n, i) &*& lseg(n, 0, count - i);
    {
        //@ open lseg(n, 0, count - i);
        n = n->next;
        i++;
        //@ lseg_tail_add(head);
    }
    //@ open lseg(0, 0, _);
    //@ lseg_to_nodes(head);
    //@ close stack(stack, count);
    return i;
}

/*@
    lemma void concatenate_lseg(struct node *head0)
        requires lseg(head0, ?head1, ?count0) &*& lseg(head1, 0, ?count1) &*& count0 >= 0;
        ensures lseg(head0, 0, count0 + count1);
    {
        if (count0 == 0)
        {
            open lseg(head0, _, _);
        }
        else if (count1 == 0)
        {
            open lseg(head1, 0, _);
        }
        else
        {
            open lseg(head1, 0, count1);
            lseg_tail_add(head0);
            open lseg(head0, _, _);
            concatenate_lseg(head0->next);
            close lseg(head0, 0, count0 + count1);
        }
    }
@*/

void stack_push_all(struct stack *stack, struct stack *other)
//@ requires stack(stack, ?count) &*& stack(other, ?count0);
//@ ensures stack(stack, count0 + count);
{
    //@ open stack(other, count0);
    struct node *head0 = other->head;
    free(other);
    struct node *n = head0;
    //@ nodes_to_lseg(head0);
    //@ open lseg(head0, 0, _);
    if (n != 0) {
        //@ close lseg(head0, head0, 0);
        while (n->next != 0)
            //@ invariant n != 0 &*& lseg(head0, n, ?count_aux) &*& malloc_block_node(n) &*& n->next |-> ?next &*& n->value |-> ?value &*& lseg(next, 0, count0 - count_aux - 1);
        {
            n = n->next;
            //@ lseg_tail_add(head0);
            //@ open lseg(next, 0, _);
        }
        //@ open stack(stack, count);
        n->next = stack->head;
        //@ nodes_to_lseg(stack->head);
        //@ close lseg(n, 0, count + 1);
        //@ open lseg(0,0,_);
        //@ concatenate_lseg(head0);
        stack->head = head0;
        //@ lseg_to_nodes(stack->head);
        //@ close stack(stack, count0 + count);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_pop(s);
    stack_pop(s);
    stack_dispose(s);
    return 0;
}
