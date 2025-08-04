@echo off
echo Building Hanoi VSCode extension...

REM Install dependencies if node_modules doesn't exist
if not exist "node_modules" (
    echo Installing dependencies...
    npm install
)

REM Compile TypeScript
echo Compiling TypeScript...
npm run compile

REM Check if compilation was successful
if %ERRORLEVEL% EQU 0 (
    echo Compilation successful!
    
    REM Package the extension
    echo Packaging extension...
    npx vsce package
    
    if %ERRORLEVEL% EQU 0 (
        echo Extension packaged successfully!
        echo You can now install the .vsix file in VSCode
    ) else (
        echo Failed to package extension
        exit /b 1
    )
) else (
    echo Compilation failed!
    exit /b 1
) 