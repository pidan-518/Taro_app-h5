@IF EXIST "%~dp0\node.exe" (
  "%~dp0\node.exe"  "%~dp0\..\@tarojs\mini-runner\node_modules\less\bin\lessc" %*
) ELSE (
  @SETLOCAL
  @SET PATHEXT=%PATHEXT:;.JS;=;%
  node  "%~dp0\..\@tarojs\mini-runner\node_modules\less\bin\lessc" %*
)