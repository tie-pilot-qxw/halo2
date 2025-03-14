//! For profiling

use std::time;

use lazy_static::lazy_static;

lazy_static! {
  static ref ZERO: time::Instant = time::Instant::now();
}

/// An interval for intrusive profiling
#[derive(Clone, Copy, Debug)]
pub struct Interval<'a>(&'a str);

impl<'a> Interval<'_> {
  /// Print beginning instant for an interval
  pub fn begin(name: &'a str) -> Interval<'a> {
    println!("Begin {}: {}", name, ZERO.elapsed().as_micros());
    Interval(name)
  }
  /// Print ending instant for an interval
  pub fn end(self) {
    println!("End {}: {}", self.0, ZERO.elapsed().as_micros());
  }
}
