/*
 * This is the source code build for Northwestern Collablab
 * PI: Darren Gergle. 
 * Project Lead: Sarah D'Angelo
 * Author: Jerry (Jiaming) Li
 * 
 * Part of the structure of this code comes from the C# example code from The Eye Tribe. 
 * I (The author) adapted it and changed to fit the need for Collablab Eyetracking research.
 * The original BSD-style license can be found in the LICENSE file in the root directory of this source tree. 
 */



using System;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Forms;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Collections.Generic;
using TETCSharpClient;
using TETCSharpClient.Data;
using MessageBox = System.Windows.MessageBox;
using System.Windows.Shapes;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading;
using System.Text.RegularExpressions;
using System.Windows.Media.Effects;



namespace EyeTrackerInterface
{
    public partial class MainWindow : IGazeListener
    {
        #region Variables
        // Constants for display
        private const float DPI_DEFAULT = 96f; // default system DIP setting
        private const double ACTIVE_SCROLL_AREA = 0.25; // 25% top and bottom
        private ImageButton latestSelection; // Records which button we pressed last.
        private readonly double dpiScale; 
        private Matrix transfrm; // The matrix that basically transforms the coordinates into x/y format that fits the screen
        // Constants for file names and recording frequency
        private string fileDirectory= Directory.GetCurrentDirectory();//output file directory
        private string fileName = @"GazeData";//output file name. Will automatically add .txt at the end
        private const int recordEveryXTime = 3;//The default is 30Hz so if recordEveryXTime = 3 then it records every 0.1 seconds
        private int recordEveryXTimeCounter = 0; // Helper variable... The record function records everytime this counter is divisible by 3
        private bool isRecording = false, shouldRecord=false;//isRecording: whether the user pressed the record button. shouldRecord: whether the user entered their laptop number. If they haven't we shouldn't start recording
        // Time and random variables
        private DateTime startTime = System.DateTime.Now;//used to disable DoButtonCheck in the first half a second
        private DateTime nowTime = System.DateTime.Now; //Just a temporary variable to get the current time. It was used a lot in many functions so I just defined a global variable for it. 
        private DateTime lastTime = System.DateTime.Now;//used to record the interval between each record.
        Random rnd = new Random();
        // Variables for recording coordinates
        private static int listmax = 80,speedlistmax = 10;//The max number of coordinates that will be recorded. Used for recording eye trace/heatmap/smoothing
        private int lasti = 0, lasti_Receiver = 0, lasti_speed = 0, lasti_Receiver_speed = 0;//Records the position of latest gaze point in xlist and ylist
        private int this_x=0, this_y = 0; // Temporary variable to record the current coordinates.
        private int[] xlist = new int[listmax], ylist = new int[listmax];//the list goes in loops and record the starting point of most recent point
        private int[] xlist_Receiver = new int[listmax], ylist_Receiver = new int[listmax]; //same as the previous lists. Records the received coordinates when communicating with program running on other computers.
        private int[] xlist_smoothing = new int[listmax], ylist_smoothing = new int[listmax]; //Similar to above
        private double[] speedlist = new double[listmax]; //list of speed. Not really useful now. Used to test some algorithms in smoothing coordinates
        private static int x_received, y_received; //coordinates of received gaze.
        private static int cursor_x_received, cursor_y_received; //coordinates of received cursor
        private string laptop_num = "-1";
        // Variables for focus effect.
        //private volatile List<focusEffectData> focusEffectDataList = new List<focusEffectData>();
        private focusEffectData focusEffectData=null;
        private Dictionary<Tuple<int,int>,int> focusEffectDataXYDict= new Dictionary<Tuple<int,int>,int>();
        // Variables for pressing buttons
        private int gazeOn = 0; // Indicate if the gaze is turned on.
        private bool traceOn = false; // Indicate if the heatmap is turned on.
        private bool SenderOn = false;//Indicate if the button Sender is pressed.
        private bool ReceiverOn = false;//Indicate if the button Receiver is pressed
        private bool CursorOn = false;//Indicate if the button Cursor is pressed
        // Constants/Variables for inter-program communication
        private static int ReceiverPort = 11000, SenderPort = 11000;//ReceiverPort is the port used by Receiver, SenderPort is the port used by Sender
        private bool communication_started_Receiver = false;//indicates whether the Receiver is ready to receive message(coordinates). Used for thread control
        private bool communication_started_Sender = false;//Indicate whether the program is sending its coordinates to others. Used for thread control
        private System.Threading.Thread communicateThread_Receiver; //Thread for receiver
        private System.Threading.Thread communicateThread_Sender;   //Thread for sender
        private static string SenderIP = "", ReceiverIP = ""; //The IP's for sender and receiver.
        private static string defaultSenderIP = "169.254.41.115"; //The default IP for sending messages. Change this to "" if you'd like to enter your IP everytime
        //SenderIP = "169.254.251.137"; //seahorse laptop. (Name of one of the two laptops we're using)
        //SenderIP = "169.254.41.115"; //Jellyfish laptop
        private static string IPpat = @"(\d+)(\.)(\d+)(\.)(\d+)(\.)(\d+)\s+"; // regular expression used for matching ip address
        private Regex r = new Regex(IPpat, RegexOptions.IgnoreCase);//regular expression variable
        private static string NumPat = @"(\d+)\s+"; 
        private Regex regex_num = new Regex(NumPat, RegexOptions.IgnoreCase);
        private System.Windows.Threading.DispatcherTimer dispatcherTimer;
        #endregion

        #region Enums

        public enum DeviceCap
        {
            /// <summary>
            /// Logical pixels inch in X
            /// </summary>
            LOGPIXELSX = 88,
            /// <summary>
            /// Logical pixels inch in Y
            /// </summary>
            LOGPIXELSY = 90
        }

        #endregion

        #region Constructor

        public MainWindow()
        {

            var connectedOk = true;
            GazeManager.Instance.Activate(GazeManager.ApiVersion.VERSION_1_0, GazeManager.ClientMode.Push);
            GazeManager.Instance.AddGazeListener(this);
            // Check status of EyeTracker
            if (!GazeManager.Instance.IsActivated)
            {
                Dispatcher.BeginInvoke(new Action(() => MessageBox.Show("EyeTribe Server has not been started")));
                connectedOk = false;
            }
            
            if (!connectedOk)
            {
                Close();
                return;
            }
            InitializeComponent();

            Touch.FrameReported += new TouchFrameEventHandler(Touch_FrameReported);

            // Register for mouse clicks
            PreviewMouseDown += TapDown;
            PreviewMouseUp += TapUp;
            // Register for key events
            KeyDown += WindowKeyDown;
            KeyUp += WindowKeyUp;

            // Get the current DIP scale
            dpiScale = CalcDpiScale();
            // Start timer


            // Write file header
            string[] lines = { "Test at " + System.DateTime.Now.ToString()+",", ""};
            try { System.IO.File.AppendAllLines(fileDirectory + fileName + ".csv", lines);
            }
            catch (Exception e)
            {
                Console.WriteLine("An error occurred: '{0}'", e);
            }

            Loaded += (sender, args) =>
            {
                // Transformation matrix that accomodate for the DPI settings
                var presentationSource = PresentationSource.FromVisual(this);
                transfrm = presentationSource.CompositionTarget.TransformFromDevice;
            };

            //Initialize the size of outside rectangle to size of the screen.
            var relativePt = new Point(Screen.PrimaryScreen.Bounds.Width, Screen.PrimaryScreen.Bounds.Height);
            relativePt = transfrm.Transform(relativePt);
            outsideRect.Rect = new Rect(0, 0, Screen.PrimaryScreen.Bounds.Width, Screen.PrimaryScreen.Bounds.Height);
            blurPath.Height = Screen.PrimaryScreen.Bounds.Height;
            blurPath.Width = Screen.PrimaryScreen.Bounds.Width;
            //  DispatcherTimer setup
            dispatcherTimer = new System.Windows.Threading.DispatcherTimer();
            dispatcherTimer.Tick += new EventHandler(update);
            dispatcherTimer.Interval = new TimeSpan(0,0,0, 0, 100);
            dispatcherTimer.Start();
            //var focusThread = new System.Threading.Thread(new ThreadStart(() => gazeFocusEffect()));
            //focusThread.Start();
            //blurEffect(100, 100);
        }

        #endregion

        #region Public methods
        // Run when gaze is received
        public void OnGazeUpdate(GazeData gazeData)
        {
            var x = (int)Math.Round(gazeData.SmoothedCoordinates.X, 0);
            var y = (int)Math.Round(gazeData.SmoothedCoordinates.Y, 0);
            if (x == 0 & y == 0) return;
            this_x = x;
            this_y = y;
            

            //record the value of coordinates to file everytime when the counter counts upto the value set by the user
            if ((isRecording))
            {
                if (shouldRecord == false)
                {
                    // If there are specific patterns you'd want for the laptop_num, uncomment this section
                    //try
                    //{
                    //    laptop_num = Data_Record_Pop_TextBox.Text;
                    //    Match m = regex_num.Match(laptop_num);
                    //    if (m.Success)
                    //    {
                    //        Data_Record_Pop.IsOpen = false;
                    //        string tempString = m.ToString();
                    //        laptop_num = tempString.TrimEnd(tempString[tempString.Length - 1]);
                    //    }
                    //}
                    //catch (Exception e)
                    //{
                    //    Console.WriteLine("An error occurred: '{0}'", e);
                    //}
                    
                }
                else if ((recordEveryXTimeCounter % recordEveryXTime == 0))
                {
                    string[] lines = { "Client Num:, "+laptop_num+", X: ," + x + ", Y: ," + y + ",Time: ," + gazeData.TimeStampString };
                    try { System.IO.File.AppendAllLines(fileDirectory + fileName + ".csv", lines); }
                    catch (Exception e)
                    {
                        Console.WriteLine("An error occurred: '{0}'", e);
                    }

                    if (ReceiverOn && x_received > 0 && y_received > 0)
                    {

                        string[] lines_Received = { "Client Num: ," + laptop_num + ", X_Received: ," + x_received + ", Y_Received: ," + y_received+ ",Time: ," + gazeData.TimeStampString };
                        try { System.IO.File.AppendAllLines(fileDirectory + fileName + ".csv", lines_Received); }
                        catch (Exception e)
                        {
                            Console.WriteLine("An error occurred: '{0}'", e);
                        }
                    }
                }
                recordEveryXTimeCounter++;
                }
            
        }

        #endregion

        #region Private methods
        // All the handlers for Mouse/keyboards
        private void TapDown(object sender, MouseButtonEventArgs e)
        {
            DoTapDown();
        }
        private void TapUp(object sender, MouseButtonEventArgs e)
        {
            DoTapUp();
        }
        private void WindowKeyDown(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (e.Key == Key.VolumeDown || e.Key == Key.VolumeUp || e.Key == Key.Escape)
                Close();
            if ((e.KeyboardDevice.IsKeyDown(Key.A)) && (e.KeyboardDevice.IsKeyDown(Key.LeftShift)) && (e.KeyboardDevice.IsKeyDown(Key.LeftAlt)))
            {
                if (GridTop.Opacity == 0)
                {
                    GridTop.Opacity = 0.8;
                    
                }
                else
                {
                    Sender_Pop.IsOpen = false;
                    GridTop.Opacity = 0;
                }
            }
            //DoTapDown();
        }

        private void WindowKeyUp(object sender, System.Windows.Input.KeyEventArgs e)
        {
            //DoTapUp();
        }
        private void DoTapDown()
        {
        }
        private void DoTapUp()
        {
            if (GridTop.Opacity != 0)//if the window is open and visible
            {
                MouseDoButtonCheck(System.Windows.Forms.Cursor.Position.X, System.Windows.Forms.Cursor.Position.Y);
                // Hide panlel and exe button click if needed
                var selectedButton = latestSelection;
                if (selectedButton != null)
                {
                    ExecuteSelectedButton(selectedButton.Name);
                }
            }
            
        }
        //touch screen implementation of TapUp
        void Touch_FrameReported(object sender, TouchFrameEventArgs e)
        {
            if (e.GetPrimaryTouchPoint(this.canvas_overlay) != null)
            {
                TouchPoint _touchPoint = e.GetPrimaryTouchPoint(this.canvas_overlay);
                if (_touchPoint.Action == TouchAction.Up)
                {
                    //Copied from DoTapUp
                    if (GridTop.Opacity != 0)//if the window is open and visible
                    {

                        MouseDoButtonCheck(Convert.ToInt32(_touchPoint.Position.X),Convert.ToInt32( _touchPoint.Position.Y));
                        // Hide panlel and exe button click if needed
                        var selectedButton = latestSelection;
                        if (selectedButton != null)
                        {
                            ExecuteSelectedButton(selectedButton.Name);
                        }
                    }
                }
            }
        }

        void update(object sender, EventArgs e)
        {
            //If user pressed Receiver or Cursor button but communication haven't started yet or has terminated, start a thread on tryCommunicateReceiver()
            if ((CursorOn||ReceiverOn) && communication_started_Receiver == false)
            {
                communication_started_Receiver = true;
                communicateThread_Receiver = new System.Threading.Thread(new ThreadStart(() => tryCommunicateReceiver(this_x, this_y)));
                communicateThread_Receiver.Start();
            }

            //If user pressed Sender button but communication haven't started yet or has terminated, start a thread on tryCommunicateSender()
            if (SenderOn && communication_started_Sender == false)
            {
                communication_started_Sender = true;
                communicateThread_Sender = new System.Threading.Thread(new ThreadStart(() => tryCommunicateSender(this_x, this_y)));
                communicateThread_Sender.Start();
            }
            // Invoke thread
            //Console.WriteLine(System.Windows.Forms.Control.MousePosition.ToString());
            Dispatcher.BeginInvoke(System.Windows.Threading.DispatcherPriority.Normal, new Action(() => UpdateUI(this_x, this_y)));

            
        }

        private void ExecuteSelectedButton(string selectedButtonName)
        {
            if (selectedButtonName == null) return;
            switch (selectedButtonName)
            {
                    // If exit is pressed
                case "exit":
                    try
                    {
                        communicateThread_Receiver.Abort();
                        communicateThread_Sender.Abort();
                    }
                    catch (Exception e)
                    {
                        Console.WriteLine(e.ToString());
                    }
                    Close();
                    break;
                // If user wants to turn on/off gaze
                case "gaze":
                    gazeOn = (gazeOn+1)%3;
                    if (gazeOn==0)
                    {
                        Gaze_Status_Text.Text = "Gaze On Focus On";
                        canvas_overlay.Visibility = System.Windows.Visibility.Visible;
                        BitmapImage bimage = new BitmapImage();
                        bimage.BeginInit();
                        bimage.UriSource = new Uri("Graphics/skyrim with focus.png", UriKind.Relative);
                        bimage.EndInit();
                        gaze.Icon = bimage;
                        //the following one is slow comparatively
                        //startrecording.Icon = new ImageSourceConverter().ConvertFromString("pack://application:,,,Graphics/stop-red-icon.png") as ImageSource;
                    }
                    else if (gazeOn==1)
                    {
                        Gaze_Status_Text.Text = "Gaze On Focus Off";
                        //remove rectangle
                        if (focusEffectData != null)
                        {
                            focusEffectDataXYDict.Remove(new Tuple<int, int>(focusEffectData.x, focusEffectData.y));
                            focusEffectData.rect.Visibility = System.Windows.Visibility.Hidden;
                            LayoutRoot.Children.Remove(focusEffectData.rect);
                            focusEffectData = null;
                        }
                        //change image
                        BitmapImage bimage = new BitmapImage();
                        bimage.BeginInit();
                        bimage.UriSource = new Uri("Graphics/skyrim.png", UriKind.Relative);
                        bimage.EndInit();
                        gaze.Icon = bimage;
                        //startrecording.Icon = new ImageSourceConverter().ConvertFromString("pack://application:,,,Graphics/start-icon.png") as ImageSource;
                    }
                    else if (gazeOn == 2)
                    {
                        Gaze_Status_Text.Text = "Gaze Off";
                        canvas_overlay.Visibility = System.Windows.Visibility.Hidden;
                        BitmapImage bimage = new BitmapImage();
                        bimage.BeginInit();
                        bimage.UriSource = new Uri("Graphics/basic_eye_closed-512.png", UriKind.Relative);
                        bimage.EndInit();
                        gaze.Icon = bimage;
                        //startrecording.Icon = new ImageSourceConverter().ConvertFromString("pack://application:,,,Graphics/start-icon.png") as ImageSource;
                    }
                    break;
                // If user want to start/stop recording
                case "startrecording":
                    isRecording = !isRecording;
                    if (isRecording)
                    {
                        Data_Record_Status_Text.Text = "Data Record On";
                        Data_Record_Pop.IsOpen = true;
                        Data_Record_Pop_TextBox.Text = "Please enter the number on this laptop";
                        BitmapImage bimage = new BitmapImage();
                        bimage.BeginInit();
                        bimage.UriSource = new Uri("Graphics/stop-red-icon.png", UriKind.Relative);
                        bimage.EndInit();
                        startrecording.Icon = bimage;
                        //the following one is slow comparatively
                        //startrecording.Icon = new ImageSourceConverter().ConvertFromString("pack://application:,,,Graphics/stop-red-icon.png") as ImageSource;
                    }
                    else
                    {
                        shouldRecord = false;
                        Data_Record_Status_Text.Text = "Data Record Off";
                        Data_Record_Pop.IsOpen = false;
                        BitmapImage bimage = new BitmapImage();
                        bimage.BeginInit();
                        bimage.UriSource = new Uri("Graphics/start-icon.png", UriKind.Relative);
                        bimage.EndInit();
                        startrecording.Icon = bimage;
                        //startrecording.Icon = new ImageSourceConverter().ConvertFromString("pack://application:,,,Graphics/start-icon.png") as ImageSource;
                    }
                    break;
                // If user want to show/hide the heatmap
                case "trace":
                    traceOn = !traceOn;
                    eyeTrace.Children.Clear();
                    eyeTrace_Receiver.Children.Clear();
                    if (traceOn)
                        Trace_Status_Text.Text = "Trace On";
                    else
                        Trace_Status_Text.Text = "Trace Off";
                    break;
                // If user want to activate/deactivate the spotlight
                case "spotlight":
                    if (MyRect.IsVisible)
                    {
                        MyRect.Visibility = System.Windows.Visibility.Hidden;
                        Spotlight_Status_Text.Text = "Spotlight Off";
                    }
                    else
                    {
                        MyRect.Visibility = System.Windows.Visibility.Visible;
                        Spotlight_Status_Text.Text = "Spotlight On";
                    }
                    break;
                // If user want to activate/deactivate sending its coordinates to some other computer
                case "Sender":
                    SenderOn = !SenderOn;
                    if (!SenderOn)
                    {
                        Sender_Status_Text.Text = "Sender Off";
                        Sender_Pop.IsOpen = false;
                        SenderIP = "";
                        try
                        {
                            communicateThread_Sender.Abort();
                            
                        }
                        catch (Exception e)
                        {
                            Console.WriteLine(e.ToString());
                        }
                        communication_started_Sender = false;
                    }
                    else
                    {
                        Sender_Status_Text.Text = "Sender On";
                        if (defaultSenderIP!=""){
                            SenderIP = defaultSenderIP;
                        }
                        else
                        {
                            Sender_Pop.IsOpen = true;
                            Sender_Pop_TextBox.Text = "Please enter other's IP address";
                            Sender_Pop_TextBox.SelectAll();
                        }
                        communication_started_Sender = false;
                    }
                    break;
                // If user want to receive message from other computer
                case "Receiver":
                    ReceiverOn = !ReceiverOn;
                    focusEffectDataXYDict.Clear();
                    if (!ReceiverOn)
                    {
                        GazePointer.Visibility = System.Windows.Visibility.Visible;
                        ReceiveGazePointer.Visibility = System.Windows.Visibility.Hidden;
                        Receiver_Status_Text.Text = "Receiver Off";
                        if (!CursorOn)//If receiving other's mouse is not on. Then terminate the whole connection. Otherwise leave it on.
                        {
                            ReceiverIP = "";
                            try
                            {
                                communicateThread_Receiver.Abort();

                            }
                            catch (Exception e)
                            {
                                Console.WriteLine(e.ToString());
                            }
                            communication_started_Receiver = false;
                        }
                        
                    }
                    else
                    {
                        GazePointer.Visibility = System.Windows.Visibility.Hidden;
                        ReceiveGazePointer.Visibility = System.Windows.Visibility.Visible;
                        IPHostEntry ipHostInfo = Dns.GetHostByName(Dns.GetHostName());
                        IPAddress ipAddress = ipHostInfo.AddressList[0];
                        Receiver_Status_Text.Text = "Receiver On\nIP:" + ipAddress.ToString();
                        if (!CursorOn)
                            communication_started_Receiver = false;
                        //Receiver_Pop.IsOpen = true;
                        //Receiver_Pop_TextBox.Text = "Please enter your IP address";
                        //Receiver_Pop_TextBox.SelectAll();
                    }
                    break;
                // If user want to display the cursor of the other computer on their screen
                case "Cursor":
                    CursorOn = !CursorOn;
                    if (!CursorOn)
                    {
                        ReceiveCursor.Visibility = System.Windows.Visibility.Hidden;
                        Cursor_Status_Text.Text = "Cursor Off";
                        if (!ReceiverOn)//If receiving other's gaze is not on. Then terminate the whole connection. Otherwise leave it on.
                        {
                            ReceiverIP = "";
                            try
                            {
                                communicateThread_Receiver.Abort();

                            }
                            catch (Exception e)
                            {
                                Console.WriteLine(e.ToString());
                            }
                            communication_started_Receiver = false;
                        }
                        
                    }
                    else
                    {
                        ReceiveCursor.Visibility = System.Windows.Visibility.Visible;
                        IPHostEntry ipHostInfo = Dns.GetHostByName(Dns.GetHostName());
                        IPAddress ipAddress = ipHostInfo.AddressList[0];
                        Cursor_Status_Text.Text = "Cursor On\nIP:" + ipAddress.ToString();
                        if (!ReceiverOn)
                            communication_started_Receiver = false;
                    }
                    break;
            }
        }

        // Input: x and y coordinates.
        // Output: None. But will display the coordinates on screen/record them/call other functions if they're activated
        private void UpdateUI(int x, int y)
        {
            // Unhide the GazePointer if you want to see your gaze point
            //GazePointer.Visibility == Visibility.Visible
            
            var relativePt = new Point(x, y);
            relativePt = transfrm.Transform(relativePt);
            bool gazeSmoothingBool=false;
            if (!ReceiverOn)
            {
                gazeSmoothingBool= gazeSmoothing(relativePt.X, relativePt.Y);
                if (gazeSmoothingBool)
                {
                    Canvas.SetLeft(GazePointer, relativePt.X - GazePointer.Width / 2);
                    Canvas.SetTop(GazePointer, relativePt.Y - GazePointer.Height / 2);
                }
                else
                {
                    try
                    {
                        addGazeFocus(Convert.ToInt32(Canvas.GetLeft(GazePointer) + GazePointer.Width / 2), Convert.ToInt32(Canvas.GetTop(GazePointer) + GazePointer.Height / 2));
                    }
                    catch
                    {
                        Console.WriteLine("error in addGazeFocus");
                    }
                }

                //********************TEST*************************
                gazeFocusEffect();
                //blurEffect(relativePt.X, relativePt.Y);
                //********************TEST*************************

            }
            else{
                if (x_received > 0 && y_received > 0)
                    {
                        gazeSmoothingBool = gazeSmoothing(x_received, y_received);
                    }
            }

            //the system will crash if one stares at the screen the whole time when it first starts. 
            //so DoButtonCheck must not be ran initially
            nowTime = System.DateTime.Now;
            if (nowTime.Subtract(startTime).TotalSeconds > 5)
            {
                if (TestBox.Opacity > 0.0)
                    TestBox.Opacity = 0.0;
                if (this.Topmost==false)
                    this.Topmost = true;
                //DoButtonCheck(x, y);
                if (MyRect.Visibility == System.Windows.Visibility.Visible)
                    changeMask(x, y);
                if (ReceiverOn)
                {
                    if (x_received > 0 && y_received > 0)
                    {
                        receiveGaze(x_received, y_received);
                    }

                    //********************TEST*************************
                    if (!gazeSmoothingBool)
                    {
                        try
                        {
                            addGazeFocus(Convert.ToInt32(x_received + GazePointer.Width / 2), Convert.ToInt32(y_received + GazePointer.Height / 2));
                        }
                        catch
                        {
                            Console.WriteLine("error in addGazeFocus");
                        }
                    }
                    gazeFocusEffect();
                    //blurEffect(relativePt.X, relativePt.Y);
                    //********************TEST*************************
                }
                if (traceOn && gazeSmoothingBool)
                {
                    
                    if (ReceiverOn && x_received > 0 && y_received > 0)
                    {
                        heatMap_Receiver(x_received, y_received);
                    }
                    else if (!ReceiverOn)
                    {
                        heatMap(x, y);
                    }
                }

                
                if (CursorOn)
                {
                    if (cursor_x_received > 0 && cursor_y_received > 0)
                    {
                        receiveCursor(cursor_x_received, cursor_y_received);
                    }
                }
                checkSenderIP();
                //checkReceiverIP();
                checkClientNum();
                
            }
            else
            {
                if (nowTime.Subtract(startTime).TotalSeconds < 4)
                    TestBox.Opacity = 1.0;
                else
                    TestBox.Opacity = (5.0 - nowTime.Subtract(startTime).TotalSeconds);
                TestBox.Text = "Please Press Left Shift + Left Alt + A to open up/close the option window.";   
            }
        }
        // Check if the coordinate is over any button. No longer used. It was used when we used the gaze to activate/deactivate a button, so you had to stare at a button to click it 
        private void DoButtonCheck(int x, int y)
        {
            var pt = new Point(x, y);
            pt = transfrm.Transform(pt);
            var foundCandidate = false;
            foreach (var child in GridButtons.Children.Cast<ImageButton>())
            {
                var isChecked = HitTest(child, pt);
                //var isChecked = HitTest(child, pt);
                child.IsChecked = isChecked;
                if (!isChecked)
                {
                    //
                    continue;
                }
                else
                {
                    GridTop.Opacity = 0.4;
                    foundCandidate = true;
                    latestSelection = child;
                    continue;
                }

            }
            if (!foundCandidate)
            {
                GridTop.Opacity = 0;
                latestSelection = null;
            }
        }
        // Check if the input coordinate is over any button
        private bool HitTest(ImageButton control, Point gazePt)
        {
            try
            {
                var gridPt = transfrm.Transform(control.PointToScreen(new Point(0, 0)));
                return gazePt.X > gridPt.X && gazePt.X < gridPt.X + control.ActualWidth &&
                gazePt.Y > gridPt.Y && gazePt.Y < gridPt.Y + control.ActualHeight;
            }
            catch (Exception e)
            {
                Console.WriteLine(e.ToString());
                return false;
            }
        }
        // Check if the mouse coordinate is over any button.
        private void MouseDoButtonCheck(int x, int y)
        {
            var pt = new Point(x, y);
            pt = transfrm.Transform(pt);
            var foundCandidate = false;
            foreach (var child in GridButtons.Children.Cast<ImageButton>())
            {
                var isChecked = MouseHitTest(child, pt);
                //var isChecked = HitTest(child, pt);
                child.IsChecked = isChecked;
                if (!isChecked)
                {
                    //
                    continue;
                }
                else
                {
                    //GridTop.Opacity = 0.2;
                    foundCandidate = true;
                    latestSelection = child;
                    continue;
                }

            }
            if (!foundCandidate)
            {
                //GridTop.Opacity = 0;
                latestSelection = null;
            }
        }
        // Check if the mouse coordinate is over one specific button.
        private bool MouseHitTest(ImageButton control, Point mousePt)
        {
            try
            {
                var gridPt = transfrm.Transform(control.PointToScreen(new Point(0, 0)));
                return mousePt.X > gridPt.X && mousePt.X < gridPt.X + control.ActualWidth &&
                mousePt.Y > gridPt.Y && mousePt.Y < gridPt.Y + control.ActualHeight;
            }
            catch (Exception e)
            {
                Console.WriteLine(e.ToString());
                return false;
            }
        }
        
        private static void CleanUp()
        {
            GazeManager.Instance.Deactivate();
            
        }
        // Called when we close the program
        protected override void OnClosing(System.ComponentModel.CancelEventArgs e)
        {
            CleanUp();
            
            isRecording = false;
            shouldRecord = false;
            traceOn = false;
            SenderOn = false;
            ReceiverOn = false;
            try
            {
                communicateThread_Receiver.Abort();
                communicateThread_Sender.Abort();
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.ToString());
            }
            base.OnClosing(e);
        }

        private static double CalcDpiScale()
        {
            return DPI_DEFAULT / GetSystemDpi().X;
        }
        //This function takes in the coordinates of received gaze and draw it onto the screen.
        private void receiveGaze(int x, int y)
        {
            if (ReceiveGazePointer.Visibility == Visibility.Visible)
            {
                var relativePt = new Point(x, y);
                relativePt = transfrm.Transform(relativePt);
                Canvas.SetLeft(ReceiveGazePointer, relativePt.X - ReceiveGazePointer.Width / 2);
                Canvas.SetTop(ReceiveGazePointer, relativePt.Y - ReceiveGazePointer.Height / 2);
                //send to textbox the coordinates in real time and the recording status
                
            }
            else { TestBox.Text = "Receiver's side Not Visible"; }
        }

        //This function takes in the coordinates of received gaze and draw it onto the screen.
        private void receiveCursor(int x, int y)
        {
            if (ReceiveCursor.Visibility == Visibility.Visible)
            {
                var relativePt = new Point(x, y);
                relativePt = transfrm.Transform(relativePt);
                Canvas.SetLeft(ReceiveCursor, relativePt.X - ReceiveCursor.Width / 2);
                Canvas.SetTop(ReceiveCursor, relativePt.Y - ReceiveCursor.Height / 2);
                //send to textbox the coordinates in real time and the recording status

            }
            else { TestBox.Text = "Receiver's side Not Visible"; }
        }
        //this draws the spot light effect on canvas
        private void changeMask(int x, int y)
        {
            RadialGradientBrush gradient1 = new RadialGradientBrush();

            gradient1.Center = new Point(1.0 * x / MyRect.ActualWidth, 1.0 * y / MyRect.ActualHeight);
            gradient1.GradientOrigin = new Point(1.0 * x / MyRect.ActualWidth, 1.0 * y / MyRect.ActualHeight);
            gradient1.RadiusX = 0.1;
            gradient1.RadiusY = 0.1 * MyRect.ActualWidth / MyRect.ActualHeight;

            GradientStop color1 = new GradientStop();
            color1.Color = Colors.Transparent;
            color1.Offset = 0;
            gradient1.GradientStops.Add(color1);

            GradientStop color2 = new GradientStop();
            color2.Color = Colors.Black;
            color2.Offset = 1;
            gradient1.GradientStops.Add(color2);
            MyRect.Fill = gradient1;
        }
        //This func records the location of gazes and show them with a halo effect
        private void heatMap(int x, int y)
        {
            //the list forms a loop with the starting point advance 1 at a time
            xlist[lasti] = x;
            ylist[lasti] = y;
            Ellipse[] ellipses = new Ellipse[listmax];
            eyeTrace.Children.Clear();
            for (int i = 0; i < listmax; i++)
            {
                ellipses[i] = new Ellipse();
                if (i <= lasti)//the most recent dot has the clearest color, so we need to have two seperate situations for the loop
                {
                    ellipses[i].Width = 50 * (listmax - lasti + i) / listmax;
                    ellipses[i].Height = 50 * (listmax - lasti + i) / listmax;
                }
                else
                {
                    ellipses[i].Width = 50 * (i - lasti - 1) / listmax;
                    ellipses[i].Height = 50 * (i - lasti - 1) / listmax;
                }
                

                //ellipses[i].Name = i.ToString();
                var relativePt = new Point(xlist[i], ylist[i]);
                relativePt = transfrm.Transform(relativePt);
                Canvas.SetLeft(ellipses[i], relativePt.X - ellipses[i].Width / 2);
                Canvas.SetTop(ellipses[i], relativePt.Y - ellipses[i].Height / 2);

                RadialGradientBrush gradient1 = new RadialGradientBrush();

                gradient1.Center = new Point(0.5, 0.5);
                gradient1.GradientOrigin = new Point(0.5, 0.5);
                gradient1.RadiusX = 0.2;
                gradient1.RadiusY = 0.2;

                GradientStop color1 = new GradientStop();
                Color color1sub = new Color();
                byte tempbyte;
                if (i <= lasti)//the most recent dot has the clearest color, so we need to have two seperate situations for the loop
                {
                    tempbyte = Convert.ToByte((listmax - lasti + i) * 255.0 / listmax);
                }
                else
                {
                    tempbyte = Convert.ToByte((i - lasti - 1) * 255.0 / listmax);
                }
                color1sub.A = Convert.ToByte(Convert.ToInt32(tempbyte)/2);
                color1sub.R = Convert.ToByte(255-Convert.ToInt32(tempbyte));
                color1sub.G = Convert.ToByte(255-Convert.ToInt32(tempbyte) );
                color1sub.B = Convert.ToByte(255-Convert.ToInt32(tempbyte) );
                color1.Color = color1sub;
                color1.Offset = 0;

                gradient1.GradientStops.Add(color1);
                GradientStop color2 = new GradientStop();
                color2.Color = Colors.Transparent;
                color2.Offset = 1;
                gradient1.GradientStops.Add(color2);
                ellipses[i].Fill = gradient1;
                eyeTrace.Children.Add(ellipses[i]);
            }

            lasti = (lasti + 1) % listmax;
        }
        
        //This func records the location of gazes Received from another Client and show them with a halo effect
        private void heatMap_Receiver(int x, int y)
        {
            //the list forms a loop with the starting point advance 1 at a time
            xlist_Receiver[lasti_Receiver] = x;
            ylist_Receiver[lasti_Receiver] = y;
            Ellipse[] ellipses = new Ellipse[listmax];
            eyeTrace_Receiver.Children.Clear();
            for (int i = 0; i < listmax; i++)
            {
                ellipses[i] = new Ellipse();
                if (i <= lasti)//the most recent dot has the clearest color, so we need to have two seperate situations for the loop
                {
                    ellipses[i].Width = 50 * (listmax - lasti + i) / listmax;
                    ellipses[i].Height = 50 * (listmax - lasti + i) / listmax;
                }
                else
                {
                    ellipses[i].Width = 50 * (i - lasti - 1) / listmax;
                    ellipses[i].Height = 50 * (i - lasti - 1) / listmax;
                }

                //ellipses[i].Name = i.ToString();
                var relativePt = new Point(xlist_Receiver[i], ylist_Receiver[i]);
                relativePt = transfrm.Transform(relativePt);
                Canvas.SetLeft(ellipses[i], relativePt.X - ellipses[i].Width / 2);
                Canvas.SetTop(ellipses[i], relativePt.Y - ellipses[i].Height / 2);

                RadialGradientBrush gradient1 = new RadialGradientBrush();
                //Draw a round gradient
                gradient1.Center = new Point(0.5, 0.5);
                gradient1.GradientOrigin = new Point(0.5, 0.5);
                gradient1.RadiusX = 0.2;
                gradient1.RadiusY = 0.2;

                GradientStop color1 = new GradientStop();
                Color color1sub = new Color();
                byte tempbyte;
                if (i <= lasti_Receiver)//the most recent dot has the clearest color, so we need to have two seperate situations for the loop
                {
                    tempbyte = Convert.ToByte((listmax - lasti_Receiver + i) * 255.0 / listmax);
                }
                else
                {
                    tempbyte = Convert.ToByte((i - lasti_Receiver - 1) * 255.0 / listmax);
                }
                // ARGB values
                color1sub.A = Convert.ToByte(Convert.ToInt32(tempbyte) / 2);
                color1sub.R = Convert.ToByte(255 - Convert.ToInt32(tempbyte));
                color1sub.G = Convert.ToByte(255 - Convert.ToInt32(tempbyte));
                color1sub.B = Convert.ToByte(255 - Convert.ToInt32(tempbyte));
                color1.Color = color1sub;
                color1.Offset = 0;

                gradient1.GradientStops.Add(color1);
                GradientStop color2 = new GradientStop();
                color2.Color = Colors.Transparent;
                color2.Offset = 1;
                gradient1.GradientStops.Add(color2);
                ellipses[i].Fill = gradient1;
                eyeTrace_Receiver.Children.Add(ellipses[i]);
            }

            lasti_Receiver = (lasti_Receiver + 1) % listmax;
        }

        //This func records the gaze and try to smooth it by setting a threshold on velocity. Returns True if the gaze is considered as moving.
        private bool gazeSmoothing(double x, double y)
        {
            //the list forms a loop with the starting point advance 1 at a time
            
            nowTime = System.DateTime.Now;
            double timeElapsed = nowTime.Subtract(lastTime).TotalMilliseconds; //milliseconds
            lastTime = System.DateTime.Now;
            xlist_smoothing[lasti_speed] = Convert.ToInt32(x);
            ylist_smoothing[lasti_speed] = Convert.ToInt32(y);
            if (lasti_speed > 0)
                speedlist[lasti_speed] = Math.Sqrt((x - xlist_smoothing[lasti_speed - 1]) * (x - xlist_smoothing[lasti_speed - 1]) +
                (y - ylist_smoothing[lasti_speed - 1]) * (y - ylist_smoothing[lasti_speed - 1])) / timeElapsed;
            //record the current value for next iteration
            else
                speedlist[lasti_speed] = Math.Sqrt((x - xlist_smoothing[speedlistmax - 1]) * (x - xlist_smoothing[speedlistmax - 1]) +
                (y - ylist_smoothing[speedlistmax - 1]) * (y - ylist_smoothing[speedlistmax - 1])) / timeElapsed;

            // NOTE: Alter this 0.1 value to do more/less smoothing
            if (speedlist[lasti_speed] > 0.1 || speedlist[lasti_speed]*timeElapsed>50)
            {
                TestBox.Text = speedlist.Max().ToString();
                lasti_speed = (lasti_speed + 1) % speedlistmax;
                return true;
            }
            else
            {
                TestBox.Text = speedlist.Max().ToString();
                lasti_speed = (lasti_speed + 1) % speedlistmax;
                return false;
            }
            
        }
        
        //This func adds the point to the list of focus points. If One of the points is repeated more than 10 times, the program will think the person is staring
        //at that point and select it to be the new focus.
        private void addGazeFocus(int x, int y)
        {
            if (gazeOn != 0)
                return;
            // Solved bug: The gaze and the rectangle is added multiple times to the list, because the program is called by a timer multiple times.
            var tupleXY = new Tuple<int, int>(x, y);
            if (!focusEffectDataXYDict.ContainsKey(tupleXY))
            {
                focusEffectDataXYDict[tupleXY] = 1;
            }
            else if (focusEffectDataXYDict[tupleXY] < 10){
                focusEffectDataXYDict[tupleXY]+=1;
            }
            else{
                if (focusEffectDataXYDict.Count > 1)
                {
                    focusEffectDataXYDict.Clear();
                    focusEffectDataXYDict[tupleXY] = 10;
                }
                
                var rect = new Rectangle();
                rect.Height = 500;
                rect.Width = 500;
                rect.Stroke = Brushes.Black;
                // How to update the left and top of the rectangle without a canvas.
                // http://stackoverflow.com/questions/8457267/rectangle-shape-wont-update-left-or-top-positions-with-canvas
                rect.Margin = new Thickness(x - rect.Width / 2, y - rect.Height / 2, 0, 0);
                rect.HorizontalAlignment = System.Windows.HorizontalAlignment.Left;
                rect.VerticalAlignment = VerticalAlignment.Top;
                nowTime = DateTime.Now;
                if (focusEffectData == null)
                {
                    focusEffectData = new focusEffectData(x, y, nowTime, rect);
                    LayoutRoot.Children.Add(rect);
                }
                
            }
        }


        //This func creates a shrinking rectangle around the stared point to get the user's attention.
        private void gazeFocusEffect()
        {
            if (focusEffectData!=null && gazeOn==0)
            {
                DateTime nowTime;
                double timeElapsed;
                nowTime = System.DateTime.Now;
                timeElapsed = nowTime.Subtract(focusEffectData.startTime).TotalMilliseconds; //milliseconds
                if (timeElapsed >= 1000)
                {
                    focusEffectDataXYDict.Remove(new Tuple<int, int>(focusEffectData.x, focusEffectData.y));
                    LayoutRoot.Children.Remove(focusEffectData.rect);
                    focusEffectData = null;
                }
                else
                {
                    try
                    {

                        focusEffectData.rect.Height = (1000 - timeElapsed);
                        focusEffectData.rect.Width = (1000 - timeElapsed);
                        focusEffectData.rect.Margin = new Thickness(focusEffectData.x - focusEffectData.rect.Width / 2, focusEffectData.y - focusEffectData.rect.Height / 2, 0, 0);
                                
                        //Canvas.SetLeft(focusEffectDataList[i].rect, focusEffectDataList[i].x);
                        //Canvas.SetTop(focusEffectDataList[i].rect, focusEffectDataList[i].y);
                        //Grid.SetRow(ScheduleRectangle, y1);
                        //Grid.SetColumn(ScheduleRectangle, x1);
                        //LayoutRoot.Children
                    }
                    catch
                    {
                        Console.WriteLine();
                    }
                        
                }
            }
            
        }

        //This func creates a shrinking rectangle around the stared point to get the user's attention.
        private void blurEffect(double x, double y)
        {
            if (blurCanvas.Visibility == System.Windows.Visibility.Hidden) 
                blurCanvas.Visibility = System.Windows.Visibility.Visible;
            //set screenshot as the background for blurring'
            blurCanvas.Opacity = 0.0;
            blurPath.UpdateLayout();
            System.Drawing.Bitmap bmp = TakeSnapshot();
            ImageBrush fill = new ImageBrush(BitmapToImageSource(bmp));
            blurPath.Fill = fill;
            blurPath.UpdateLayout();
            bmp.Dispose();
            transparentEclipse.Center = new Point(x, y);
            blurCanvas.Opacity = 1.0;
        }

        private static System.Drawing.Bitmap Blur(System.Drawing.Bitmap image, System.Drawing.Rectangle rectangle, Int32 blurSize)
        {
            System.Drawing.Bitmap blurred = new System.Drawing.Bitmap(image.Width, image.Height);

            // make an exact copy of the bitmap provided
            using (System.Drawing.Graphics graphics = System.Drawing.Graphics.FromImage(blurred))
                graphics.DrawImage(image, new System.Drawing.Rectangle(0, 0, image.Width, image.Height),
                    new System.Drawing.Rectangle(0, 0, image.Width, image.Height), System.Drawing.GraphicsUnit.Pixel);

            // look at every pixel in the blur rectangle
            for (Int32 xx = rectangle.X; xx < rectangle.X + rectangle.Width; xx++)
            {
                for (Int32 yy = rectangle.Y; yy < rectangle.Y + rectangle.Height; yy++)
                {
                    Int32 avgR = 0, avgG = 0, avgB = 0;
                    Int32 blurPixelCount = 0;

                    // average the color of the red, green and blue for each pixel in the
                    // blur size while making sure you don't go outside the image bounds
                    for (Int32 x = xx; (x < xx + blurSize && x < image.Width); x++)
                    {
                        for (Int32 y = yy; (y < yy + blurSize && y < image.Height); y++)
                        {
                            System.Drawing.Color pixel = blurred.GetPixel(x, y);

                            avgR += pixel.R;
                            avgG += pixel.G;
                            avgB += pixel.B;

                            blurPixelCount++;
                        }
                    }

                    avgR = avgR / blurPixelCount;
                    avgG = avgG / blurPixelCount;
                    avgB = avgB / blurPixelCount;

                    // now that we know the average for the blur size, set each pixel to that color
                    for (Int32 x = xx; x < xx + blurSize && x < image.Width && x < rectangle.Width; x++)
                        for (Int32 y = yy; y < yy + blurSize && y < image.Height && y < rectangle.Height; y++)
                            blurred.SetPixel(x, y, System.Drawing.Color.FromArgb(avgR, avgG, avgB));
                }
            }

            return blurred;
        }

        private static System.Drawing.Bitmap TakeSnapshot()
        {
            int w = Convert.ToInt32(Screen.PrimaryScreen.Bounds.Width), h = Convert.ToInt32(Screen.PrimaryScreen.Bounds.Height);
            Console.WriteLine(Screen.PrimaryScreen.Bounds.Width);
            System.Drawing.Bitmap bmp = new System.Drawing.Bitmap(w,h);
            using (System.Drawing.Graphics g = System.Drawing.Graphics.FromImage(bmp))
            {
                g.CopyFromScreen(0,0,0,0,
                    new System.Drawing.Size(w,h));
            }//6,6 is the offset. Otherwise the screen is cut off a little bit.
            return bmp;
        }

        private static BitmapImage BitmapToImageSource(System.Drawing.Bitmap bitmap)
        {
            using (MemoryStream memory = new MemoryStream())
            {
                bitmap.Save(memory, System.Drawing.Imaging.ImageFormat.Bmp);
                memory.Position = 0;
                BitmapImage bitmapimage = new BitmapImage();
                bitmapimage.BeginInit();
                bitmapimage.StreamSource = memory;
                bitmapimage.CacheOption = BitmapCacheOption.OnLoad;
                bitmapimage.EndInit();

                return bitmapimage;
            }
        }

        #endregion

        #region Other Private methods
        //this func checks if the ip in the textbox is correctly formatted. Called everytime user opens up Client
        private void checkSenderIP()
        {
            try
            {
                //if the Sender is just turned on
                //can't access this because another thread owns the object. Cannot be put under onGazeUpdate.
                if (SenderOn == true && Sender_Pop != null && Sender_Pop.IsOpen == true)
                {
                    string Input_Sender_IP = Sender_Pop_TextBox.Text;
                    Match m = r.Match(Input_Sender_IP);
                    if (m.Success)
                    {
                        Sender_Pop.IsOpen = false;
                        string tempString = m.ToString();
                        SenderIP = tempString.TrimEnd(tempString[tempString.Length - 1]);
                    }
                }
            }
            catch (Exception e)
            {
                Console.WriteLine("An error occurred: '{0}'", e);

            }
        }

        //this func checks if the client number in the textbox is correctly formatted. Client number is used to name the clients so that we could tell which trial we're doing.
        private void checkClientNum()
        {
            string temp_num = Data_Record_Pop_TextBox.Text;
            Match m = regex_num.Match(temp_num);
            if (m.Success)
            {
                Data_Record_Pop.IsOpen = false;
                string tempString = m.ToString();
                laptop_num = tempString.TrimEnd(tempString[tempString.Length - 1]);
                shouldRecord = true;
            }
        }

        #endregion

        #region Native methods

        public static Point GetSystemDpi()
        {
            Point result = new Point();
            IntPtr hDc = GetDC(IntPtr.Zero);
            result.X = GetDeviceCaps(hDc, (int)DeviceCap.LOGPIXELSX);
            result.Y = GetDeviceCaps(hDc, (int)DeviceCap.LOGPIXELSY);
            ReleaseDC(IntPtr.Zero, hDc);
            return result;
        }

        [DllImport("gdi32.dll")]
        private static extern int GetDeviceCaps(IntPtr hdc, int nIndex);

        [DllImport("user32.dll")]
        private static extern IntPtr GetDC(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern int ReleaseDC(IntPtr hWnd, IntPtr hDc);

        #endregion

        #region Sender/Receiver Methods

        public void tryCommunicateReceiver(int x, int y)
        {
            IPHostEntry ipHostInfo = Dns.Resolve(Dns.GetHostName());
            ReceiverIP = ipHostInfo.AddressList[0].ToString();
            //x_received = 0;
            //y_received = 0;
            //AsynchronousClient.StartClient(x, y);
            while (ReceiverIP == "")
            {
                System.Threading.Thread.Sleep(1000);
            }
            AsynchronousSocketListener.StartListening();


        }
        public void tryCommunicateSender(int x, int y)
        {
            while (SenderIP == "")
            {
                System.Threading.Thread.Sleep(1000);
            }
            SynchronousClient.StartClient(x, y);
            communication_started_Sender = false;

            //AsynchronousSocketListener.StartListening();

            //receiveGaze(x_received, y_received);
        }
        public class StateObject
        {
            // Client  socket.
            public Socket workSocket = null;
            // Size of receive buffer.
            public const int BufferSize = 1024;
            // Receive buffer.
            public byte[] buffer = new byte[BufferSize];
            // Received data string.
            public StringBuilder sb = new StringBuilder();
        }
        //THis is the Receiver function (Asyncronous)
        // Citation: https://msdn.microsoft.com/en-us/library/fx6588te%28v=vs.110%29.aspx
        public class AsynchronousSocketListener
        {
            // Thread signal.
            public static ManualResetEvent allDone = new ManualResetEvent(false);

            public AsynchronousSocketListener()
            {
            }

            public static void StartListening()
            {
                if (ReceiverIP != "")
                {

                    // Data buffer for incoming data.
                    byte[] bytes = new Byte[1024];

                    // Establish the local endpoint for the socket.
                    // The DNS name of the computer
                    IPHostEntry ipHostInfo = Dns.Resolve(Dns.GetHostName());
                    IPAddress ipAddress = IPAddress.Parse(ReceiverIP);
                    IPEndPoint localEndPoint = new IPEndPoint(ipAddress, ReceiverPort);

                    // Create a TCP/IP socket.
                    Socket listener = new Socket(AddressFamily.InterNetwork,
                        SocketType.Stream, ProtocolType.Tcp);

                    // Bind the socket to the local endpoint and listen for incoming connections.
                    try
                    {
                        listener.Bind(localEndPoint);
                        listener.Listen(100);
                        //ommunication_received==false
                        while (true)
                        {
                            // Set the event to nonsignaled state.
                            allDone.Reset();

                            // Start an asynchronous socket to listen for connections.
                            //Console.WriteLine("Waiting for a connection...");
                            listener.BeginAccept(
                                new AsyncCallback(AcceptCallback),
                                listener);

                            allDone.WaitOne();

                            // Wait until a connection is made before continuing.


                        }

                    }
                    catch (Exception e)
                    {
                        Console.WriteLine(e.ToString());
                    }

                    //Console.WriteLine("\nPress ENTER to continue...");
                    //Console.Read();

                }
            }

            public static void AcceptCallback(IAsyncResult ar)
            {
                // Signal the main thread to continue.
                allDone.Set();

                // Get the socket that handles the client request.
                Socket listener = (Socket)ar.AsyncState;
                Socket handler = listener.EndAccept(ar);

                // Create the state object.
                StateObject state = new StateObject();
                state.workSocket = handler;
                handler.BeginReceive(state.buffer, 0, StateObject.BufferSize, 0,
                    new AsyncCallback(ReadCallback), state);
            }

            public static void ReadCallback(IAsyncResult ar)
            {
                String content = String.Empty;

                // Retrieve the state object and the handler socket
                // from the asynchronous state object.
                StateObject state = (StateObject)ar.AsyncState;
                Socket handler = state.workSocket;

                // Read data from the client socket. 
                int bytesRead = handler.EndReceive(ar);

                if (bytesRead > 0)
                {
                    // There  might be more data, so store the data received so far.
                    state.sb.Append(Encoding.ASCII.GetString(
                        state.buffer, 0, bytesRead));

                    // Check for end-of-file tag. If it is not there, read 
                    // more data.
                    content = state.sb.ToString();
                    if (content.IndexOf("<EOF>") > -1)
                    {
                        // All the data has been read from the 
                        // client. Display it on the console.
                        int x_start_ind = content.IndexOf("x: "), x_end_ind = content.IndexOf("xend ");
                        int y_start_ind = content.IndexOf("y: "), y_end_ind = content.IndexOf("yend ");
                        int cursor_x_start_ind = content.IndexOf("cursorx: "), cursor_x_end_ind = content.IndexOf("cursorxend ");
                        int cursor_y_start_ind = content.IndexOf("cursory: "), cursor_y_end_ind = content.IndexOf("cursoryend ");
                        if (x_start_ind > -1 && x_end_ind > -1 && y_start_ind > -1 && y_end_ind > -1)
                        {
                            try
                            {
                                //convert the received string into x and y                                
                                x_received = Convert.ToInt32(content.Substring(x_start_ind + 3, x_end_ind - (x_start_ind + 3)));
                                y_received = Convert.ToInt32(content.Substring(y_start_ind + 3, y_end_ind - (y_start_ind + 3)));
                            }
                            catch (FormatException)
                            {
                                Console.WriteLine("Input string is not a sequence of digits.");
                            }
                            catch (OverflowException)
                            {
                                Console.WriteLine("The number cannot fit in an Int32.");
                            }
                        }
                        if (cursor_x_start_ind > -1 && cursor_x_end_ind > -1 && cursor_y_start_ind > -1 && cursor_y_end_ind > -1)
                        {
                            try
                            {
                                cursor_x_received = Convert.ToInt32(
                                    content.Substring(cursor_x_start_ind + 9, cursor_x_end_ind - (cursor_x_start_ind + 9)));
                                cursor_y_received = Convert.ToInt32(
                                    content.Substring(cursor_y_start_ind + 9, cursor_y_end_ind - (cursor_y_start_ind + 9)));
                            }
                            catch (FormatException)
                            {
                                Console.WriteLine("Input string is not a sequence of digits.");
                            }
                            catch (OverflowException)
                            {
                                Console.WriteLine("The number cannot fit in an Int32.");
                            }
                        }
                        // Show the data on the console.
                        //Console.WriteLine("x : {0}  y: {1}", x_received, y_received);

                        // Echo the data back to the client.
                        Send(handler, content);
                    }
                    else
                    {
                        // Not all data received. Get more.
                        handler.BeginReceive(state.buffer, 0, StateObject.BufferSize, 0,
                        new AsyncCallback(ReadCallback), state);
                    }
                }
            }

            private static void Send(Socket handler, String data)
            {
                // Convert the string data to byte data using ASCII encoding.
                byte[] byteData = Encoding.ASCII.GetBytes(data);

                // Begin sending the data to the remote device.
                handler.BeginSend(byteData, 0, byteData.Length, 0,
                    new AsyncCallback(SendCallback), handler);
            }

            private static void SendCallback(IAsyncResult ar)
            {
                try
                {
                    // Retrieve the socket from the state object.
                    Socket handler = (Socket)ar.AsyncState;

                    // Complete sending the data to the remote device.
                    int bytesSent = handler.EndSend(ar);
                    //Console.WriteLine("Sent {0} bytes to client.", bytesSent);x

                    handler.Shutdown(SocketShutdown.Both);
                    handler.Close();

                }
                catch (Exception e)
                {
                    Console.WriteLine(e.ToString());
                }
            }
        }
        //This is the sending function (Syncronous)
        public class SynchronousClient
        {

            public static void StartClient(int x, int y)
            {
                // Data buffer for incoming data.
                byte[] bytes = new byte[1024];

                // Connect to a remote device.
                try
                {
                    // Establish the remote endpoint for the socket.
                    // This example uses port 11000 on the local computer.
                    IPHostEntry ipHostInfo = Dns.GetHostByName(Dns.GetHostName());
                    IPAddress ipAddress = IPAddress.Parse(SenderIP); 
                    IPEndPoint remoteEP = new IPEndPoint(ipAddress, SenderPort);
                    
                    // Create a TCP/IP  socket.
                    Socket sender = new Socket(AddressFamily.InterNetwork,
                        SocketType.Stream, ProtocolType.Tcp);

                    // Connect the socket to the remote endpoint. Catch any errors.
                    try
                    {
                        sender.Connect(remoteEP);

                        Console.WriteLine("Socket connected to {0}",
                            sender.RemoteEndPoint.ToString());
                        string message_being_sent = "x: " + x + "xend y: " + y + "yend cursorx: " +
                            System.Windows.Forms.Cursor.Position.X + "cursorxend cursory: " + 
                            System.Windows.Forms.Cursor.Position.Y + "cursoryend <EOF>";
                        // Encode the data string into a byte array.
                        byte[] msg = Encoding.ASCII.GetBytes(message_being_sent);

                        // Send the data through the socket.
                        int bytesSent = sender.Send(msg);

                        // Receive the response from the remote device.
                        int bytesRec = sender.Receive(bytes);
                        Console.WriteLine("Echoed test = {0}",
                            Encoding.ASCII.GetString(bytes, 0, bytesRec));

                        // Release the socket.
                        sender.Shutdown(SocketShutdown.Both);
                        sender.Close();

                    }
                    catch (ArgumentNullException ane)
                    {
                        Console.WriteLine("ArgumentNullException : {0}", ane.ToString());
                    }
                    catch (SocketException se)
                    {
                        Console.WriteLine("SocketException : {0}", se.ToString());
                    }
                    catch (Exception e)
                    {
                        Console.WriteLine("Unexpected exception : {0}", e.ToString());
                    }

                }
                catch (Exception e)
                {
                    Console.WriteLine(e.ToString());
                }
            }

            public static string data = null;
            public static int x_received, y_received;
            public static int cursor_x_received,cursor_y_received;
            public static void StartListening()
            {
                // Data buffer for incoming data.
                byte[] bytes = new Byte[1024];

                // Establish the local endpoint for the socket.
                // Dns.GetHostName returns the name of the 
                // host running the application.
                IPHostEntry ipHostInfo = Dns.GetHostByName(Dns.GetHostName());
                IPAddress ipAddress = IPAddress.Parse(SenderIP);  
                IPEndPoint localEndPoint = new IPEndPoint(ipAddress, SenderPort);

                // Create a TCP/IP socket.
                Socket listener = new Socket(AddressFamily.InterNetwork,
                    SocketType.Stream, ProtocolType.Tcp);

                // Bind the socket to the local endpoint and 
                // listen for incoming connections.
                try
                {
                    listener.Bind(localEndPoint);
                    listener.Listen(10);

                    // Start listening for connections.
                    while (true)
                    {
                        Console.WriteLine("Waiting for a connection...");
                        // Program is suspended while waiting for an incoming connection.
                        Socket handler = listener.Accept();
                        data = null;

                        // An incoming connection needs to be processed.
                        while (true)
                        {
                            bytes = new byte[1024];
                            int bytesRec = handler.Receive(bytes);
                            data += Encoding.ASCII.GetString(bytes, 0, bytesRec);
                            if (data.IndexOf("<EOF>") > -1)
                            {
                                break;
                            }
                        }
                        int x_start_ind = data.IndexOf("x: "), x_end_ind = data.IndexOf("xend ");
                        int y_start_ind = data.IndexOf("y: "), y_end_ind = data.IndexOf("yend ");
                        int cursor_x_start_ind = data.IndexOf("cursorx: "), cursor_x_end_ind = data.IndexOf("cursorxend ");
                        int cursor_y_start_ind = data.IndexOf("cursory: "), cursor_y_end_ind = data.IndexOf("cursoryend ");
                        if (x_start_ind > -1 && x_end_ind > -1 && y_start_ind > -1 && y_end_ind > -1)
                        {
                            try
                            {
                                x_received = Convert.ToInt32(data.Substring(x_start_ind + 2, x_end_ind - 1));
                                y_received = Convert.ToInt32(data.Substring(y_start_ind + 2, y_end_ind - 1));
                            }
                            catch (FormatException)
                            {
                                Console.WriteLine("Input string is not a sequence of digits.");
                            }
                            catch (OverflowException)
                            {
                                Console.WriteLine("The number cannot fit in an Int32.");
                            }
                        }
                        if (cursor_x_start_ind > -1 && cursor_x_end_ind > -1 && cursor_y_start_ind > -1 && cursor_y_end_ind > -1)
                        {
                            try
                            {
                                cursor_x_received = Convert.ToInt32(data.Substring(cursor_x_start_ind + 8, cursor_x_end_ind - 1));
                                cursor_y_received = Convert.ToInt32(data.Substring(cursor_y_start_ind + 8, cursor_y_end_ind - 1));
                            }
                            catch (FormatException)
                            {
                                Console.WriteLine("Input string is not a sequence of digits.");
                            }
                            catch (OverflowException)
                            {
                                Console.WriteLine("The number cannot fit in an Int32.");
                            }
                        }
                        // Show the data on the console.
                        Console.WriteLine("x : {0}  y: {1}", x_received, y_received);

                        // Echo the data back to the client.
                        byte[] msg = Encoding.ASCII.GetBytes(data);

                        handler.Send(msg);
                        handler.Shutdown(SocketShutdown.Both);
                        handler.Close();
                    }

                }
                catch (Exception e)
                {
                    Console.WriteLine(e.ToString());
                }

                Console.WriteLine("\nPress ENTER to continue...");
                Console.Read();

            }
        }

        #endregion
    }
}
