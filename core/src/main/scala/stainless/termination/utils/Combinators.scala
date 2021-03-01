package stainless
package termination
package utils

trait Combinators {
  def foldOrFail[A,B](it: Iterable[A])(zero: B)(fail: A => Boolean)(f: (B,A) => B): Option[B] = {
    val ii = it.iterator
    var b = zero
    while (ii.hasNext) {
      val x = ii.next
      if (fail(x)) return None
      b = f(b,x)
    }
    Some(b)
  }

  def foldOrSuccess[A,B](it: Iterable[A])(zero: B)(success: A => Boolean)(f: (B,A) => B): Option[B] = {
    val ii = it.iterator
    var b = zero
    while (ii.hasNext) {
      val x = ii.next
      if (success(x)) return Some(b)
      b = f(b,x)
    }
    None
  }
} 