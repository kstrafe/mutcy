pub type FractionalIndexType = u32;

#[derive(Clone, Copy)]
pub struct FractionalIndex {
    current: FractionalIndexType,
    half: FractionalIndexType,
}

impl FractionalIndex {
    pub fn new() -> Self {
        Self {
            current: FractionalIndexType::MAX / 2 + 1,
            half: FractionalIndexType::MAX / 4 + 1,
        }
    }

    pub fn left(self) -> Option<Self> {
        debug_assert!(self.current % 2 == 0);
        if self.half > 1 {
            Some(Self {
                current: self.current - self.half,
                half: self.half / 2,
            })
        } else {
            None
        }
    }

    pub fn right(self) -> Option<Self> {
        debug_assert!(self.current % 2 == 0);
        if self.half > 1 {
            Some(Self {
                current: self.current + self.half,
                half: self.half / 2,
            })
        } else {
            None
        }
    }

    pub fn value(self) -> FractionalIndexType {
        self.current
    }
}
