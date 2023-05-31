use honggfuzz::fuzz;
use ante::util::timing::start_time;


fn main() {
    honggfuzz::fuzz!(|data: &[u8]| {
        // Convert the fuzz input to a string or use any other relevant conversion logic
        let input_str = String::from_utf8_lossy(data);

        // Call the start_time function with the fuzzed input
        start_time(&input_str);
    });
}