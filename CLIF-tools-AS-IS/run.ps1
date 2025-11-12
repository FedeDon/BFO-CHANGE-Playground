Write-Host "Starting Parser and Reasoner execution..."

# Force file system sync
Write-Host "Forcing file system sync..."
[System.GC]::Collect()
[System.GC]::WaitForPendingFinalizers()

Write-Host "Running parser.pl..."
swipl -s "BFO2020style-CLIFparser.pl" -g "main, halt"

Write-Host "Running reasoner.pl..."  
swipl -s "BFO2020style-CLIFreasoner - Working20250415.pl" -g "run, halt"

Write-Host "Batch execution completed!"
pause