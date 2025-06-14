pub type FractionalIndexType = u128;

#[derive(Clone, Copy)]
pub struct FractionalIndex {
    current: FractionalIndexType,
    half: FractionalIndexType,
}

impl FractionalIndex {
    pub fn new() -> Self {
        Self {
            current: FractionalIndexType::MAX / 2,
            half: FractionalIndexType::MAX / 4 + 1,
        }
    }

    pub fn left(self) -> Option<Self> {
        if self.half > 0 {
            Some(Self {
                current: self.current - self.half,
                half: self.half / 2,
            })
        } else {
            None
        }
    }

    pub fn right(self) -> Option<Self> {
        if self.half > 0 {
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
