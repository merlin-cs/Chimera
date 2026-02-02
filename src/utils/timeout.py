import signal
from types import FrameType
from typing import Optional

class TimeoutException(Exception): 
    pass 

# Define the handler function
def handler(signum: int, frame: Optional[FrameType]) -> None: 
    """
    Signal handler for timeout.
    
    Args:
        signum: The signal number.
        frame: The current stack frame.
    
    Raises:
        TimeoutException
    """
    raise TimeoutException()

def register_timeout_handler() -> None:
    """
    Register the timeout handler for SIGALRM.
    """
    # Register the handler function
    signal.signal(signal.SIGALRM, handler)
